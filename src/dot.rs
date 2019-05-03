use std::fmt::{Display, Formatter, Result};

use crate::{egraph::EGraph, expr::Language};

pub struct Dot<'a, L: Language> {
    egraph: &'a EGraph<L>,
}

impl<'a, L: Language> Dot<'a, L> {
    pub fn new(egraph: &EGraph<L>) -> Dot<L> {
        Dot { egraph }
    }
}

impl<'a, L: Language> Display for Dot<'a, L>
where
    L::Constant: Display,
    L::Variable: Display,
    L::Operator: Display,
{
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "digraph {{\n")?;

        // set compound=true to enable edges to clusters
        write!(f, "  compound=true\n")?;

        // define all the nodes, clustered by eclass
        for (leader, class) in &self.egraph.classes {
            write!(f, "  subgraph cluster_{} {{\n", leader)?;
            write!(f, "    style=dotted\n")?;
            for (i, node) in class.iter().enumerate() {
                write!(f, "    {}.{}[label = \"{}\"]\n", leader, i, node.symbol())?;
            }
            write!(f, "  }}\n")?;
        }

        for (leader, class) in &self.egraph.classes {
            for (i_in_class, node) in class.iter().enumerate() {
                for (arg_i, child) in node.children().iter().enumerate() {
                    // write the edge to the child, but clip it to the eclass with lhead
                    let child_leader = self.egraph.leaders.just_find(*child);
                    write!(
                        f,
                        // {}.0 to pick an arbitrary node in the cluster
                        "  {}.{} -> {}.0 [lhead = cluster_{}, label = {}]\n",
                        leader, i_in_class, child, child_leader, arg_i
                    )?;
                }
            }
        }

        write!(f, "}}")
    }
}