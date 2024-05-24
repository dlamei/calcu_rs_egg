use fmt::Formatter;
use log::*;
use std::borrow::Cow;
use std::fmt::{self, Display};
use std::{convert::TryFrom, str::FromStr};

use thiserror::Error;

use crate::*;

/// A pattern that can function as either a [`Searcher`] or [`Applier`].
///
/// A [`Pattern`] is essentially a for-all quantified expression with
/// [`Var`]s as the variables (in the logical sense).
///
/// When creating a [`Rewrite`], the most common thing to use as either
/// the left hand side (the [`Searcher`]) or the right hand side
/// (the [`Applier`]) is a [`Pattern`].
///
/// As a [`Searcher`], a [`Pattern`] does the intuitive
/// thing.
/// Here is a somewhat verbose formal-ish statement:
/// Searching for a pattern in an egraph yields substitutions
/// ([`Subst`]s) _s_ such that, for any _s'_—where instead of
/// mapping a variables to an eclass as _s_ does, _s'_ maps
/// a variable to an arbitrary expression represented by that
/// eclass—_p[s']_ (the pattern under substitution _s'_) is also
/// represented by the egraph.
///
/// As an [`Applier`], a [`Pattern`] performs the given substitution
/// and adds the result to the [`EGraph`].
///
/// Importantly, [`Pattern`] implements [`FromStr`] if the
/// [`Language`] does.
/// This is probably how you'll create most [`Pattern`]s.
///
/// ```
/// use egg::*;
/// define_language! {
///     enum Math {
///         Num(i32),
///         "+" = Add([Id; 2]),
///     }
/// }
///
/// let mut egraph = EGraph::<Math, ()>::default();
/// let a11 = egraph.add_expr(&"(+ 1 1)".parse().unwrap());
/// let a22 = egraph.add_expr(&"(+ 2 2)".parse().unwrap());
///
/// // use Var syntax (leading question mark) to get a
/// // variable in the Pattern
/// let same_add: Pattern<Math> = "(+ ?a ?a)".parse().unwrap();
///
/// // Rebuild before searching
/// egraph.rebuild();
///
/// // This is the search method from the Searcher trait
/// let matches = same_add.search(&egraph);
/// let matched_eclasses: Vec<Id> = matches.iter().map(|m| m.eclass).collect();
/// assert_eq!(matched_eclasses, vec![a11, a22]);
/// ```
///
/// [`FromStr`]: std::str::FromStr
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Pattern<L> {
    /// The actual pattern as a [`RecExpr`]
    pub ast: PatternAst<L>,
    program: machine::Program<L>,
}

/// A [`RecExpr`] that represents a
/// [`Pattern`].
pub type PatternAst<L> = RecExpr<ENodeOrVar<L>>;

impl<L: Language> PatternAst<L> {
    /// Returns a new `PatternAst` with the variables renames canonically
    pub fn alpha_rename(&self) -> Self {
        let mut vars = HashMap::<Var, Var>::default();
        let mut new = PatternAst::default();

        fn mkvar(i: usize) -> Var {
            let vs = &["?x", "?y", "?z", "?w"];
            match vs.get(i) {
                Some(v) => v.parse().unwrap(),
                None => format!("?v{}", i - vs.len()).parse().unwrap(),
            }
        }

        for n in self.as_ref() {
            new.add(match n {
                ENodeOrVar::ENode(_) => n.clone(),
                ENodeOrVar::Var(v) => {
                    let i = vars.len();
                    ENodeOrVar::Var(*vars.entry(*v).or_insert_with(|| mkvar(i)))
                }
            });
        }

        new
    }
}

impl Pattern<Expr> {
    /// Creates a new pattern from the given pattern ast.
    pub fn new(ast: PatternAst<Expr>) -> Self {
        let ast = ast.compact();
        let program = machine::Program::compile_from_pat(&ast);
        Pattern { ast, program }
    }

    /// Returns a list of the [`Var`]s in this pattern.
    pub fn vars(&self) -> Vec<Var> {
        let mut vars = vec![];
        for n in self.ast.as_ref() {
            if let ENodeOrVar::Var(v) = n {
                if !vars.contains(v) {
                    vars.push(*v)
                }
            }
        }
        vars
    }
}

impl<L: Language + Display> Pattern<L> {
    /// Pretty print this pattern as a sexp with the given width
    pub fn pretty(&self, width: usize) -> String {
        self.ast.pretty(width)
    }
}

/// The language of [`Pattern`]s.
///
#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum ENodeOrVar<L> {
    /// An enode from the underlying [`Language`]
    ENode(L),
    /// A pattern variable
    Var(Var),
}

/// The discriminant for the language of [`Pattern`]s.
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum ENodeOrVarDiscriminant<L: Language> {
    ENode(L::Discriminant),
    Var(Var),
}

impl<L: Language> Language for ENodeOrVar<L> {
    type Discriminant = ENodeOrVarDiscriminant<L>;

    #[inline(always)]
    fn discriminant(&self) -> Self::Discriminant {
        match self {
            ENodeOrVar::ENode(n) => ENodeOrVarDiscriminant::ENode(n.discriminant()),
            ENodeOrVar::Var(v) => ENodeOrVarDiscriminant::Var(*v),
        }
    }

    fn matches(&self, _other: &Self) -> bool {
        panic!("Should never call this")
    }

    fn children(&self) -> &[Id] {
        match self {
            ENodeOrVar::ENode(n) => n.children(),
            ENodeOrVar::Var(_) => &[],
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            ENodeOrVar::ENode(n) => n.children_mut(),
            ENodeOrVar::Var(_) => &mut [],
        }
    }
}

impl<L: Language + Display> Display for ENodeOrVar<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ENode(node) => Display::fmt(node, f),
            Self::Var(var) => Display::fmt(var, f),
        }
    }
}

#[derive(Debug, Error)]
pub enum ENodeOrVarParseError<E> {
    #[error(transparent)]
    BadVar(<Var as FromStr>::Err),

    #[error("tried to parse pattern variable {0:?} as an operator")]
    UnexpectedVar(String),

    #[error(transparent)]
    BadOp(E),
}

//impl<L: FromOp> FromOp for ENodeOrVar<L> {
//    type Error = ENodeOrVarParseError<L::Error>;
//
//    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
//        use ENodeOrVarParseError::*;
//
//        if op.starts_with('?') && op.len() > 1 {
//            if children.is_empty() {
//                op.parse().map(Self::Var).map_err(BadVar)
//            } else {
//                Err(UnexpectedVar(op.to_owned()))
//            }
//        } else {
//            L::from_op(op, children).map(Self::ENode).map_err(BadOp)
//        }
//    }
//}

//impl<L: FromOp> std::str::FromStr for Pattern<L> {
//    type Err = RecExprParseError<ENodeOrVarParseError<L::Error>>;
//
//    fn from_str(s: &str) -> Result<Self, Self::Err> {
//        PatternAst::from_str(s).map(Self::from)
//    }
//}

impl<'a> From<&'a [Expr]> for Pattern<Expr> {
    fn from(expr: &'a [Expr]) -> Self {
        let nodes: Vec<_> = expr.iter().cloned().map(ENodeOrVar::ENode).collect();
        let ast = RecExpr::from(nodes);
        Self::new(ast)
    }
}

impl From<&RecExpr<Expr>> for Pattern<Expr> {
    fn from(expr: &RecExpr<Expr>) -> Self {
        Self::from(expr.as_ref())
    }
}

impl From<PatternAst<Expr>> for Pattern<Expr> {
    fn from(ast: PatternAst<Expr>) -> Self {
        Self::new(ast)
    }
}

impl<L: Language> TryFrom<Pattern<L>> for RecExpr<L> {
    type Error = Var;
    fn try_from(pat: Pattern<L>) -> Result<Self, Self::Error> {
        let nodes = pat.ast.as_ref().iter().cloned();
        let ns: Result<Vec<_>, _> = nodes
            .map(|n| match n {
                ENodeOrVar::ENode(n) => Ok(n),
                ENodeOrVar::Var(v) => Err(v),
            })
            .collect();
        ns.map(RecExpr::from)
    }
}

impl<L: Language + Display> Display for Pattern<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.ast, f)
    }
}

/// The result of searching a [`Searcher`] over one eclass.
///
/// Note that one [`SearchMatches`] can contain many found
/// substitutions. So taking the length of a list of [`SearchMatches`]
/// tells you how many eclasses something was matched in, _not_ how
/// many matches were found total.
///
#[derive(Debug)]
pub struct SearchMatches<'a, L: Language> {
    /// The eclass id that these matches were found in.
    pub eclass: Id,
    /// The substitutions for each match.
    pub substs: Vec<Subst>,
    /// Optionally, an ast for the matches used in proof production.
    pub ast: Option<Cow<'a, PatternAst<L>>>,
}

impl Searcher<Expr, ConstFolding> for Pattern<Expr> {
    fn get_pattern_ast(&self) -> Option<&PatternAst<Expr>> {
        Some(&self.ast)
    }

    fn search_with_limit(&self, egraph: &EGraph, limit: usize) -> Vec<SearchMatches<Expr>> {
        match self.ast.as_ref().last().unwrap() {
            ENodeOrVar::ENode(e) => {
                let key = e.discriminant();
                match egraph.classes_by_op.get(&key) {
                    None => vec![],
                    Some(ids) => rewrite::search_eclasses_with_limit(
                        self,
                        egraph,
                        ids.iter().cloned(),
                        limit,
                    ),
                }
            }
            ENodeOrVar::Var(_) => rewrite::search_eclasses_with_limit(
                self,
                egraph,
                egraph.classes().map(|e| e.id),
                limit,
            ),
        }
    }

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
            let ast = Some(Cow::Borrowed(&self.ast));
            Some(SearchMatches {
                eclass,
                substs,
                ast,
            })
        }
    }

    fn vars(&self) -> Vec<Var> {
        Pattern::vars(self)
    }
}

impl Applier<Expr, ConstFolding> for Pattern<Expr>
{
    fn get_pattern_ast(&self) -> Option<&PatternAst<Expr>> {
        Some(&self.ast)
    }

    fn apply_matches(
        &self,
        egraph: &mut EGraph,
        matches: &[SearchMatches<Expr>],
        rule_name: Symbol,
    ) -> Vec<Id> {
        let mut added = vec![];
        let ast = self.ast.as_ref();
        let mut id_buf = vec![0.into(); ast.len()];
        for mat in matches {
            let sast = mat.ast.as_ref().map(|cow| cow.as_ref());
            for subst in &mat.substs {
                let did_something;
                let id;
                if egraph.are_explanations_enabled() {
                    let (id_temp, did_something_temp) =
                        egraph.union_instantiations(sast.unwrap(), &self.ast, subst, rule_name);
                    did_something = did_something_temp;
                    id = id_temp;
                } else {
                    id = apply_pat(&mut id_buf, ast, egraph, subst);
                    did_something = egraph.union(id, mat.eclass);
                }

                if did_something {
                    added.push(id)
                }
            }
        }
        added
    }

    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Expr>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let ast = self.ast.as_ref();
        let mut id_buf = vec![0.into(); ast.len()];
        let id = apply_pat(&mut id_buf, ast, egraph, subst);

        if let Some(ast) = searcher_ast {
            let (from, did_something) =
                egraph.union_instantiations(ast, &self.ast, subst, rule_name);
            if did_something {
                vec![from]
            } else {
                vec![]
            }
        } else if egraph.union(eclass, id) {
            vec![eclass]
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        Pattern::vars(self)
    }
}

pub(crate) fn apply_pat(
    ids: &mut [Id],
    pat: &[ENodeOrVar<Expr>],
    egraph: &mut EGraph,
    subst: &Subst,
) -> Id {
    debug_assert_eq!(pat.len(), ids.len());
    trace!("apply_rec {:2?} {:?}", pat, subst);

    for (i, pat_node) in pat.iter().enumerate() {
        let id = match pat_node {
            ENodeOrVar::Var(w) => subst[*w],
            ENodeOrVar::ENode(e) => {
                let n = e.clone().map_children(|child| ids[usize::from(child)]);
                trace!("adding: {:?}", n);
                egraph.add(n)
            }
        };
        ids[i] = id;
    }

    *ids.last().unwrap()
}


