use std::str::FromStr;
use thiserror::Error;

use crate::*;

/// A set of open expressions bound to variables.
///
/// Multipatterns bind many expressions to variables,
/// allowing for simultaneous searching or application of many terms
/// constrained to the same substitution.
///
/// Multipatterns are good for writing graph rewrites or datalog-style rules.
///
/// You can create multipatterns via the [`MultiPattern::new`] function or the
/// [`multi_rewrite!`] macro.
///
/// [`MultiPattern`] implements both [`Searcher`] and [`Applier`].
/// When searching a multipattern, the result ensures that
/// patterns bound to the same variable are equivalent.
/// When applying a multipattern, patterns bound a variable occuring in the
/// searcher are unioned with that e-class.
///
/// Multipatterns currently do not support the explanations feature.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MultiPattern<L> {
    asts: Vec<(Var, PatternAst<L>)>,
    program: machine::Program<L>,
}

impl MultiPattern<Expr> {
    /// Creates a new multipattern, binding the given patterns to the corresponding variables.
    ///
    /// ```
    /// use egg::*;
    ///
    /// let mut egraph = EGraph::<SymbolLang, ()>::default();
    /// egraph.add_expr(&"(f a a)".parse().unwrap());
    /// egraph.add_expr(&"(f a b)".parse().unwrap());
    /// egraph.add_expr(&"(g a a)".parse().unwrap());
    /// egraph.add_expr(&"(g a b)".parse().unwrap());
    /// egraph.rebuild();
    ///
    /// let f_pat: PatternAst<SymbolLang> = "(f ?x ?y)".parse().unwrap();
    /// let g_pat: PatternAst<SymbolLang> = "(g ?x ?y)".parse().unwrap();
    /// let v1: Var = "?v1".parse().unwrap();
    /// let v2: Var = "?v2".parse().unwrap();
    ///
    /// let multipattern = MultiPattern::new(vec![(v1, f_pat), (v2, g_pat)]);
    /// // you can also parse multipatterns
    /// assert_eq!(multipattern, "?v1 = (f ?x ?y), ?v2 = (g ?x ?y)".parse().unwrap());
    ///
    /// assert_eq!(multipattern.n_matches(&egraph), 2);
    /// ```
    pub fn new(asts: Vec<(Var, PatternAst<Expr>)>) -> Self {
        let program = machine::Program::compile_from_multi_pat(&asts);
        Self { asts, program }
    }
}

#[derive(Debug, Error)]
/// An error raised when parsing a [`MultiPattern`]
pub enum MultiPatternParseError<E> {
    /// One of the patterns in the multipattern failed to parse.
    #[error(transparent)]
    PatternParseError(E),
    /// One of the clauses in the multipattern wasn't of the form `?var (= pattern)+`.
    #[error("Bad clause in the multipattern: {0}")]
    PatternAssignmentError(String),
    /// One of the variables failed to parse.
    #[error(transparent)]
    VariableError(<Var as FromStr>::Err),
}

//impl<L: Language + FromOp> FromStr for MultiPattern<L> {
//    type Err = MultiPatternParseError<<PatternAst<L> as FromStr>::Err>;
//
//    fn from_str(s: &str) -> Result<Self, Self::Err> {
//        use MultiPatternParseError::*;
//        let mut asts = vec![];
//        for split in s.trim().split(',') {
//            let split = split.trim();
//            if split.is_empty() {
//                continue;
//            }
//            let mut parts = split.split('=');
//            let vs: &str = parts
//                .next()
//                .ok_or_else(|| PatternAssignmentError(split.into()))?;
//            let v: Var = vs.trim().parse().map_err(VariableError)?;
//            let ps = parts
//                .map(|p| p.trim().parse())
//                .collect::<Result<Vec<PatternAst<L>>, _>>()
//                .map_err(PatternParseError)?;
//            if ps.is_empty() {
//                return Err(PatternAssignmentError(split.into()));
//            }
//            asts.extend(ps.into_iter().map(|p| (v, p)))
//        }
//        Ok(MultiPattern::new(asts))
//    }
//}

impl Searcher<Expr, ConstFolding> for MultiPattern<Expr> {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<Expr>> {
        let substs = self.program.run_with_limit(egraph, eclass, limit);
        if substs.is_empty() {
            None
        } else {
            Some(SearchMatches {
                eclass,
                substs,
                ast: None,
            })
        }
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = vec![];
        for (v, pat) in &self.asts {
            vars.push(*v);
            for n in pat.as_ref() {
                if let ENodeOrVar::Var(v) = n {
                    vars.push(*v)
                }
            }
        }
        vars.sort();
        vars.dedup();
        vars
    }
}

impl Applier<Expr, ConstFolding> for MultiPattern<Expr> {
    fn apply_one(
        &self,
        _egraph: &mut EGraph,
        _eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<Expr>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        panic!("Multipatterns do not support apply_one")
    }

    fn apply_matches(
        &self,
        egraph: &mut EGraph,
        matches: &[SearchMatches<Expr>],
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // TODO explanations?
        // the ids returned are kinda garbage
        let mut added = vec![];
        for mat in matches {
            for subst in &mat.substs {
                let mut subst = subst.clone();
                let mut id_buf = vec![];
                for (i, (v, p)) in self.asts.iter().enumerate() {
                    id_buf.resize(p.as_ref().len(), 0.into());
                    let id1 = crate::pattern::apply_pat(&mut id_buf, p.as_ref(), egraph, &subst);
                    if let Some(id2) = subst.insert(*v, id1) {
                        egraph.union(id1, id2);
                    }
                    if i == 0 {
                        added.push(id1)
                    }
                }
            }
        }
        added
    }

    fn vars(&self) -> Vec<Var> {
        let mut bound_vars = HashSet::default();
        let mut vars = vec![];
        for (bv, pat) in &self.asts {
            for n in pat.as_ref() {
                if let ENodeOrVar::Var(v) = n {
                    // using vars that are already bound doesn't count
                    if !bound_vars.contains(v) {
                        vars.push(*v)
                    }
                }
            }
            bound_vars.insert(bv);
        }
        vars.sort();
        vars.dedup();
        vars
    }
}
