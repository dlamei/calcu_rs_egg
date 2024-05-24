use pattern::apply_pat;
use std::fmt::{self, Debug};
use std::sync::Arc;

use crate::*;

/// A rewrite that searches for the lefthand side and applies the righthand side.
///
/// The [`rewrite!`] macro is the easiest way to create rewrites.
///
/// A [`Rewrite`] consists principally of a [`Searcher`] (the lefthand
/// side) and an [`Applier`] (the righthand side).
/// It additionally stores a name used to refer to the rewrite and a
/// long name used for debugging.
///
#[derive(Clone)]
#[non_exhaustive]
pub struct Rewrite {
    /// The name of the rewrite.
    pub name: Symbol,
    /// The searcher (left-hand side) of the rewrite.
    pub searcher: Arc<dyn Searcher + Sync + Send>,
    /// The applier (right-hand side) of the rewrite.
    pub applier: Arc<dyn Applier + Sync + Send>,
}

impl Debug for Rewrite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Rewrite");
        d.field("name", &self.name);

        // if let Some(pat) = Any::downcast_ref::<dyn Pattern<L>>(&self.searcher) {
        if let Some(pat) = self.searcher.get_pattern_ast() {
            d.field("searcher", &DisplayAsDebug(pat));
        } else {
            d.field("searcher", &"<< searcher >>");
        }

        if let Some(pat) = self.applier.get_pattern_ast() {
            d.field("applier", &DisplayAsDebug(pat));
        } else {
            d.field("applier", &"<< applier >>");
        }

        d.finish()
    }
}

impl Rewrite {
    /// Create a new [`Rewrite`]. You typically want to use the
    /// [`rewrite!`] macro instead.
    ///
    pub fn new(
        name: impl Into<Symbol>,
        searcher: impl Searcher + Send + Sync + 'static,
        applier: impl Applier + Send + Sync + 'static,
    ) -> Result<Self, String> {
        let name = name.into();
        let searcher = Arc::new(searcher);
        let applier = Arc::new(applier);

        let bound_vars = searcher.vars();
        for v in applier.vars() {
            if !bound_vars.contains(&v) {
                return Err(format!("Rewrite {} refers to unbound var {}", name, v));
            }
        }

        Ok(Self {
            name,
            searcher,
            applier,
        })
    }

    /// Call [`search`] on the [`Searcher`].
    ///
    /// [`search`]: Searcher::search()
    pub fn search(&self, egraph: &EGraph) -> Vec<SearchMatches<'_>> {
        self.searcher.search(egraph)
    }

    /// Call [`search_with_limit`] on the [`Searcher`].
    ///
    /// [`search_with_limit`]: Searcher::search_with_limit()
    pub fn search_with_limit(&self, egraph: &EGraph, limit: usize) -> Vec<SearchMatches<'_>> {
        self.searcher.search_with_limit(egraph, limit)
    }

    /// Call [`apply_matches`] on the [`Applier`].
    ///
    /// [`apply_matches`]: Applier::apply_matches()
    pub fn apply(&self, egraph: &mut EGraph, matches: &[SearchMatches<'_>]) -> Vec<Id> {
        self.applier.apply_matches(egraph, matches, self.name)
    }

    /// This `run` is for testing use only. You should use things
    /// from the `egg::run` module
    #[cfg(test)]
    pub(crate) fn run(&self, egraph: &mut EGraph) -> Vec<Id> {
        let start = crate::util::Instant::now();

        let matches = self.search(egraph);
        log::debug!("Found rewrite {} {} times", self.name, matches.len());

        let ids = self.apply(egraph, &matches);
        let elapsed = start.elapsed();
        log::debug!(
            "Applied rewrite {} {} times in {}.{:03}",
            self.name,
            ids.len(),
            elapsed.as_secs(),
            elapsed.subsec_millis()
        );

        egraph.rebuild();
        ids
    }
}

/// Searches the given list of e-classes with a limit.
pub(crate) fn search_eclasses_with_limit<'a, I, S>(
    searcher: &'a S,
    egraph: &EGraph,
    eclasses: I,
    mut limit: usize,
) -> Vec<SearchMatches<'a>>
where
    S: Searcher + ?Sized,
    I: IntoIterator<Item = Id>,
{
    let mut ms = vec![];
    for eclass in eclasses {
        if limit == 0 {
            break;
        }
        match searcher.search_eclass_with_limit(egraph, eclass, limit) {
            None => continue,
            Some(m) => {
                let len = m.substs.len();
                assert!(len <= limit);
                limit -= len;
                ms.push(m);
            }
        }
    }
    ms
}

/// The lefthand side of a [`Rewrite`].
///
/// A [`Searcher`] is something that can search the egraph and find
/// matching substitutions.
/// Right now the only significant [`Searcher`] is [`Pattern`].
///
pub trait Searcher {
    /// Search one eclass, returning None if no matches can be found.
    /// This should not return a SearchMatches with no substs.
    fn search_eclass(&self, egraph: &EGraph, eclass: Id) -> Option<SearchMatches<'_>> {
        self.search_eclass_with_limit(egraph, eclass, usize::MAX)
    }

    /// Similar to [`search_eclass`], but return at most `limit` many matches.
    ///
    /// Implementation of [`Searcher`] should implement
    /// [`search_eclass_with_limit`].
    ///
    /// [`search_eclass`]: Searcher::search_eclass
    /// [`search_eclass_with_limit`]: Searcher::search_eclass_with_limit
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches>;

    /// Search the whole [`EGraph`], returning a list of all the
    /// [`SearchMatches`] where something was found.
    /// This just calls [`Searcher::search_with_limit`] with a big limit.
    fn search(&self, egraph: &EGraph) -> Vec<SearchMatches> {
        self.search_with_limit(egraph, usize::MAX)
    }

    /// Similar to [`search`], but return at most `limit` many matches.
    ///
    /// [`search`]: Searcher::search
    fn search_with_limit(&self, egraph: &EGraph, limit: usize) -> Vec<SearchMatches> {
        search_eclasses_with_limit(self, egraph, egraph.classes().map(|e| e.id), limit)
    }

    /// Returns the number of matches in the e-graph
    fn n_matches(&self, egraph: &EGraph) -> usize {
        self.search(egraph).iter().map(|m| m.substs.len()).sum()
    }

    /// For patterns, return the ast directly as a reference
    fn get_pattern_ast(&self) -> Option<&PatternAst> {
        None
    }

    /// Returns a list of the variables bound by this Searcher
    fn vars(&self) -> Vec<Var>;
}

/// The righthand side of a [`Rewrite`].
///
/// An [`Applier`] is anything that can do something with a
/// substitution ([`Subst`]). This allows you to implement rewrites
/// that determine when and how to respond to a match using custom
/// logic, including access to the [`Analysis`] data of an [`EClass`].
///
/// Notably, [`Pattern`] implements [`Applier`], which suffices in
/// most cases.
/// Additionally, `egg` provides [`ConditionalApplier`] to stack
/// [`Condition`]s onto an [`Applier`], which in many cases can save
/// you from having to implement your own applier.
pub trait Applier {
    /// Apply many substitutions.
    ///
    /// This method should call [`apply_one`] for each match.
    ///
    /// It returns the ids resulting from the calls to [`apply_one`].
    /// The default implementation does this and should suffice for
    /// most use cases.
    ///
    /// [`apply_one`]: Applier::apply_one()
    fn apply_matches(
        &self,
        egraph: &mut EGraph,
        matches: &[SearchMatches],
        rule_name: Symbol,
    ) -> Vec<Id> {
        let mut added = vec![];
        for mat in matches {
            let ast = if egraph.are_explanations_enabled() {
                mat.ast.as_ref().map(|cow| cow.as_ref())
            } else {
                None
            };
            for subst in &mat.substs {
                let ids = self.apply_one(egraph, mat.eclass, subst, ast, rule_name);
                added.extend(ids)
            }
        }
        added
    }

    /// For patterns, get the ast directly as a reference.
    fn get_pattern_ast(&self) -> Option<&PatternAst> {
        None
    }

    /// Apply a single substitution.
    ///
    /// An [`Applier`] should add things and union them with `eclass`.
    /// Appliers can also inspect the eclass if necessary using the
    /// `eclass` parameter.
    ///
    /// This should return a list of [`Id`]s of eclasses that
    /// were changed. There can be zero, one, or many.
    /// When explanations mode is enabled, a [`PatternAst`] for
    /// the searcher is provided.
    ///
    /// [`apply_matches`]: Applier::apply_matches()
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst>,
        rule_name: Symbol,
    ) -> Vec<Id>;

    /// Returns a list of variables that this Applier assumes are bound.
    ///
    /// `egg` will check that the corresponding `Searcher` binds those
    /// variables.
    /// By default this return an empty `Vec`, which basically turns off the
    /// checking.
    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// An [`Applier`] that checks a [`Condition`] before applying.
///
/// A [`ConditionalApplier`] simply calls [`check`] on the
/// [`Condition`] before calling [`apply_one`] on the inner
/// [`Applier`].
///
/// See the [`rewrite!`] macro documentation for an example.
///
/// [`apply_one`]: Applier::apply_one()
/// [`check`]: Condition::check()
#[derive(Clone, Debug)]
pub struct ConditionalApplier<C, A> {
    /// The [`Condition`] to [`check`] before calling [`apply_one`] on
    /// `applier`.
    ///
    /// [`apply_one`]: Applier::apply_one()
    /// [`check`]: Condition::check()
    pub condition: C,
    /// The inner [`Applier`] to call once `condition` passes.
    ///
    pub applier: A,
}

impl<C, A> Applier for ConditionalApplier<C, A>
where
    C: Condition,
    A: Applier,
{
    fn get_pattern_ast(&self) -> Option<&PatternAst> {
        self.applier.get_pattern_ast()
    }

    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        if self.condition.check(egraph, eclass, subst) {
            self.applier
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = self.applier.vars();
        vars.extend(self.condition.vars());
        vars
    }
}

/// A condition to check in a [`ConditionalApplier`].
///
/// See the [`ConditionalApplier`] docs.
///
/// Notably, any function ([`Fn`]) that doesn't mutate other state
/// and matches the signature of [`check`] implements [`Condition`].
///
/// [`check`]: Condition::check()
/// [`Fn`]: std::ops::Fn
pub trait Condition {
    /// Check a condition.
    ///
    /// `eclass` is the eclass [`Id`] where the match (`subst`) occured.
    /// If this is true, then the [`ConditionalApplier`] will fire.
    ///
    fn check(&self, egraph: &mut EGraph, eclass: Id, subst: &Subst) -> bool;

    /// Returns a list of variables that this Condition assumes are bound.
    ///
    /// `egg` will check that the corresponding `Searcher` binds those
    /// variables.
    /// By default this return an empty `Vec`, which basically turns off the
    /// checking.
    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

impl<F> Condition for F
where
    F: Fn(&mut EGraph, Id, &Subst) -> bool,
{
    fn check(&self, egraph: &mut EGraph, eclass: Id, subst: &Subst) -> bool {
        self(egraph, eclass, subst)
    }
}

/// A [`Condition`] that checks if two terms are equivalent.
///
/// This condition adds its two [`Pattern`] to the egraph and passes
/// if and only if they are equivalent (in the same eclass).
///
#[derive(Debug)]
pub struct ConditionEqual {
    p1: Pattern,
    p2: Pattern,
}

impl ConditionEqual {
    /// Create a new [`ConditionEqual`] condition given two patterns.
    pub fn new(p1: Pattern, p2: Pattern) -> Self {
        ConditionEqual { p1, p2 }
    }
}

impl Condition for ConditionEqual {
    fn check(&self, egraph: &mut EGraph, _eclass: Id, subst: &Subst) -> bool {
        let mut id_buf_1 = vec![0.into(); self.p1.ast.as_ref().len()];
        let mut id_buf_2 = vec![0.into(); self.p2.ast.as_ref().len()];
        let a1 = apply_pat(&mut id_buf_1, self.p1.ast.as_ref(), egraph, subst);
        let a2 = apply_pat(&mut id_buf_2, self.p2.ast.as_ref(), egraph, subst);
        a1 == a2
    }

    fn vars(&self) -> Vec<Var> {
        let mut vars = self.p1.vars();
        vars.extend(self.p2.vars());
        vars
    }
}
