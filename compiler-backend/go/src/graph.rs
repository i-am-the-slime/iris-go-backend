//! Strongly connected components, which several passes need of a reference graph.

/// Tarjan's algorithm, iteratively, so that long chains do not exhaust the stack. Each
/// component is listed after every component it has an edge to, its members in the order they
/// leave the stack. `edges[node]` are the nodes `node` refers to, visited in that order.
pub fn strongly_connected(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    const UNVISITED: usize = usize::MAX;
    let count = edges.len();
    let mut index = vec![UNVISITED; count];
    let mut lowest = vec![0; count];
    let mut on_stack = vec![false; count];
    let mut stack = vec![];
    let mut components = vec![];
    let mut next = 0;
    for root in 0..count {
        if index[root] != UNVISITED {
            continue;
        }
        let mut work = vec![(root, 0usize)];
        while let Some(&mut (node, ref mut edge)) = work.last_mut() {
            if *edge == 0 && index[node] == UNVISITED {
                index[node] = next;
                lowest[node] = next;
                next += 1;
                stack.push(node);
                on_stack[node] = true;
            }
            if let Some(&target) = edges[node].get(*edge) {
                *edge += 1;
                if index[target] == UNVISITED {
                    work.push((target, 0));
                } else if on_stack[target] {
                    lowest[node] = lowest[node].min(index[target]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                lowest[parent] = lowest[parent].min(lowest[node]);
            }
            if lowest[node] == index[node] {
                let mut component = vec![];
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                components.push(component);
            }
        }
    }
    components
}

/// Whether each node lies on a cycle: it shares its component or refers to itself.
pub fn on_cycles(edges: &[Vec<usize>], components: &[Vec<usize>]) -> Vec<bool> {
    let mut cyclic = vec![false; edges.len()];
    for component in components {
        let node = component[0];
        let on_cycle = component.len() > 1 || edges[node].contains(&node);
        for &member in component {
            cyclic[member] = on_cycle;
        }
    }
    cyclic
}
