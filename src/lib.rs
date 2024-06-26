#![cfg_attr(docsrs, feature(doc_cfg))]
/*!

`egg` (**e**-**g**raphs **g**ood) is a e-graph library optimized for equality saturation.

This is the API documentation.

There is also a [paper](https://arxiv.org/abs/2004.03082)
describing `egg` and some of its technical novelties.

## Logging

Many parts of `egg` dump useful logging info using the [`log`](https://docs.rs/log/) crate.
The easiest way to see this info is to use the [`env_logger`](https://docs.rs/env_logger/)
crate in your binary or test.
The simplest way to enable `env_logger` is to put the following line near the top of your `main`:
`env_logger::init();`.
Then, set the environment variable `RUST_LOG=egg=info`, or use `warn` or `debug` instead of info
for less or more logging.

*/

mod egraph;
mod explain;
mod language;
mod machine;
mod multipattern;
mod pattern;
mod rewrite;
mod run;
mod util;

/// A key to identify [`EClass`]es within an
/// [`EGraph`].
#[derive(Clone, Copy, Default, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Id(u32);

impl From<usize> for Id {
    fn from(n: usize) -> Id {
        Id(n as u32)
    }
}

impl From<Id> for usize {
    fn from(id: Id) -> usize {
        id.0 as usize
    }
}

impl std::fmt::Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub(crate) use {explain::Explain, util::EClassUnion};

pub use {
    egraph::EClass,
    egraph::EGraph,
    explain::{
        Explanation, FlatExplanation, FlatTerm, Justification, TreeExplanation, TreeTerm,
        UnionEqualities,
    },
    language::*,
    multipattern::*,
    pattern::{ENodeOrVar, Pattern, PatternAst, SearchMatches},
    rewrite::{Applier, Condition, ConditionEqual, ConditionalApplier, Rewrite, Searcher, Var, Subst},
    run::*,
    util::*,
};

#[cfg(test)]
fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}
