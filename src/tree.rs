use std::cmp::{Ord, Ordering};

use std::fmt::{Display, Formatter};

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone)]
struct Node<K, V> {
    index: usize,
    parent: Option<usize>,
    left: Option<usize>,
    right: Option<usize>,
    key: K,
    value: V,
    color: Color,
}

impl<K, V> Node<K, V> {
    pub fn from(
        index: usize,
        parent: Option<usize>,
        left: Option<usize>,
        right: Option<usize>,
        key: K,
        value: V,
        color: Color,
    ) -> Self {
        Node {
            index,
            parent,
            left,
            right,
            key,
            value,
            color,
        }
    }
}

impl<K, V> Display for Node<K, V>
where
    K: Display,
    V: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{:?} -> {} -> ({:?}, {:?})]::{:?} ({} -> {})",
            self.parent, self.index, self.left, self.right, self.color, self.key, self.value
        )
    }
}
use std::fmt::Debug;
pub struct Tree<K, V> {
    nodes: Vec<Node<K, V>>,
    root: usize,
}

impl<K, V> Tree<K, V>
where
    K: Ord + Display + Debug,
    V: Display + Debug,
{
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            root: 0,
        }
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    // Should be a fast way to access a node at some index.
    fn at(&self, node: usize) -> &Node<K, V> {
        &self.nodes[node]
    }
    fn at_mut(&mut self, node: usize) -> &mut Node<K, V> {
        &mut self.nodes[node]
    }
    fn try_at(&self, node: usize) -> Option<&Node<K, V>> {
        self.nodes.get(node)
    }
    fn try_at_mut(&mut self, node: usize) -> Option<&mut Node<K, V>> {
        self.nodes.get_mut(node)
    }
    fn at_opt(&self, node_opt: Option<usize>) -> Option<&Node<K, V>> {
        match node_opt {
            Some(node) => self.try_at(node),
            _ => None,
        }
    }
    fn at_mut_opt(&mut self, node_opt: Option<usize>) -> Option<&mut Node<K, V>> {
        match node_opt {
            Some(node) => self.try_at_mut(node),
            _ => None,
        }
    }
    fn left_rotate(&mut self, idx: usize) -> Option<()> {
        // start -> ... x -> (a, y -> (b, c))
        // want: start -> ... y -> (x -> (a, b), c)
        let x = self.try_at(idx)?;
        let x_idx = idx;
        let a = x.left;
        let parent = x.parent;
        let y = self.try_at(x.right?)?;
        let y_idx = y.index;
        let b = y.left;

        // If there is a parent of this subtree, update its children.
        if let Some(par) = parent {
            if let Some(par_node) = self.try_at_mut(par) {
                if par_node.left.is_some() && par_node.left? == x_idx {
                    par_node.left = Some(y_idx);
                } else if par_node.right.is_some() && par_node.right? == x_idx {
                    par_node.right = Some(y_idx);
                } else {
                    panic!("X's parent does not record X as one of its children in left_rotate().");
                }
            } else {
                // x points to a parent, but it apparently doesn't exist in the tree. error.
                panic!("X points to a parent that is supposedly not in the tree.");
            }
        } else {
            // this subtree is actually the root tree. update the root to y.
            self.root = y_idx;
        }

        let x = self.try_at_mut(x_idx)?;
        x.left = a;
        x.right = b;
        x.parent = Some(y_idx);
        let y = self.try_at_mut(y_idx)?;
        y.left = Some(x_idx);
        y.parent = parent;

        // If b is a subtree, switch its parent between x and y.
        if let Some(b_node) = self.at_mut_opt(b) {
            b_node.parent = Some(x_idx);
        }

        Some(())
    }
    fn right_rotate(&mut self, idx: usize) -> Option<()> {
        // start -> ... y -> (x -> (a, b), c)
        // want: start -> ... x -> (a, y -> (b, c))
        let y = self.try_at(idx)?;
        let y_idx = idx;
        let c = y.right;
        let parent = y.parent;
        let x = self.try_at(y.left?)?;
        let x_idx = x.index;
        let b = x.right;

        // If there is a parent of this subtree, update its children.
        if let Some(par) = parent {
            if let Some(par_node) = self.try_at_mut(par) {
                if par_node.left.is_some() && par_node.left? == y_idx {
                    par_node.left = Some(x_idx);
                } else if par_node.right.is_some() && par_node.right? == y_idx {
                    par_node.right = Some(x_idx);
                } else {
                    panic!(
                        "Y's parent does not record X as one of its children in right_rotate()."
                    );
                }
            } else {
                // y points to a parent, but it apparently doesn't exist in the tree. error.
                panic!("Y points to a parent that is supposedly not in the tree.");
            }
        } else {
            // this subtree is actually the root tree.  update the root of the tree to x.
            self.root = x_idx;
        }

        let y = self.try_at_mut(y_idx)?;
        y.left = b;
        y.right = c;
        y.parent = Some(x_idx);
        let x = self.try_at_mut(x_idx)?;
        x.right = Some(y_idx);
        x.parent = parent;

        // If b is a subtree, switch its parent between x and y.
        if let Some(b_node) = self.at_mut_opt(b) {
            b_node.parent = Some(y_idx);
        }

        Some(())
    }
    fn enforce_root_black(&mut self) {
        self.nodes[self.root].color = Color::Black;
    }
    // Two ways of searching a Vec-BTree: linear, and BST search.
    // Linear is faster in practice thanks to cache locality.
    // BST is faster asymptotically.
    // We implement get() and lookup() to represent both.
    pub fn get(&self, key: &K) -> Option<&V> {
        for k in &self.nodes {
            if k.key.cmp(key) == Ordering::Equal {
                return Some(&k.value);
            }
        }
        return None;
    }
    // get_mut...
    pub fn lookup(&self, key: &K) -> Option<&V> {
        let mut cur = Some(self.root);
        while let Some(index) = cur {
            if let Some(node) = self.nodes.get(index) {
                match node.key.cmp(key) {
                    Ordering::Less => cur = node.right,   // node < key
                    Ordering::Greater => cur = node.left, // key < node
                    Ordering::Equal => return Some(&node.value),
                }
            } else {
                // Root is not present, thus this is empty.
                return None;
            }
        }
        return None;
    }
    // lookup_mut...
    // Note: maps use "mem::replace" to replace elements.
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let mut prev = None;
        let mut cur = Some(self.root);

        while let Some(index) = cur {
            if let Some(node) = self.nodes.get_mut(index) {
                prev = cur;
                match node.key.cmp(&k) {
                    Ordering::Less => cur = node.right,   // node < key
                    Ordering::Greater => cur = node.left, // key < node
                    Ordering::Equal => return Some(std::mem::replace(&mut node.value, v)),
                }
            } else {
                // Root is not present; add in new root.
                if !self.is_empty() {
                    panic!("could not find node of root index, despite self being occupied.");
                }
                self.nodes
                    .push(Node::from(self.root, None, None, None, k, v, Color::Black));
                return None;
            }
        }
        // reached nil, tree not empty, prev = Some(node) under which to place the new node.
        let index = self.nodes.len();
        let leaf = self.at_mut(
            prev.expect("ERR: prev should contain a Some(index) that points to an existing node."),
        );

        match k.cmp(&leaf.key) {
            Ordering::Less => leaf.left = Some(index),
            Ordering::Greater => leaf.right = Some(index),
            Ordering::Equal => unreachable!(),
        }
        let z = Node::from(index, prev, None, None, k, v, Color::Red);
        self.nodes.push(z);
        self.insert_fix(index);

        None
    }
    fn insert_fix(&mut self, inserted: usize) -> Option<()> {
        let mut z_idx = inserted;

        while let Some(par_idx) = self.at(z_idx).parent {
            let parent = self.at(par_idx);
            if parent.color == Color::Black {
                return Some(());
            }
            let grand_idx = parent.parent?; // if no grandparent, return; parent should be black as it is root
            let grandparent = self.at(grand_idx);
            let grand_left = grandparent.left;
            let grand_right = grandparent.right;

            // y is the uncle of z.
            // println!("parent: {}\ngrandparent: {}", parent, grandparent);

            if grand_left.is_some() && par_idx == grand_left? {
                let y = self.at_opt(grand_right);
                // case 1: z red, z.p red, z's uncle red.
                if y.is_some() && y?.color == Color::Red {
                    let y_idx = y?.index;
                    self.at_mut(par_idx).color = Color::Black;
                    self.at_mut(y_idx).color = Color::Black;
                    self.at_mut(grand_idx).color = Color::Red;
                    z_idx = grand_idx;
                } else {
                    // case 2: z is a right child, and z's uncle is black
                    if parent.right.is_some() && z_idx == parent.right? {
                        z_idx = par_idx;
                        self.left_rotate(z_idx);
                    }
                    // case 3: z is a left child, and z's uncle is black
                    let par_idx = self.at(z_idx).parent?; // can't be nil as it was grandparent
                    let grand_idx = self.at(par_idx).parent?; // can't be nil; must be colored red
                    self.at_mut(par_idx).color = Color::Black;
                    self.at_mut(grand_idx).color = Color::Red;
                    self.right_rotate(grand_idx);
                }
            } else if grand_right.is_some() && par_idx == grand_right? {
                let y = self.at_opt(grand_left);
                // case 1: z red, z.p red, z's uncle red.
                if y.is_some() && y?.color == Color::Red {
                    let y_idx = y?.index;
                    self.at_mut(par_idx).color = Color::Black;
                    self.at_mut(y_idx).color = Color::Black;
                    self.at_mut(grand_idx).color = Color::Red;
                    z_idx = grand_idx;
                } else {
                    // case 2: z is a right child, and z's uncle is black
                    if parent.left.is_some() && z_idx == parent.left? {
                        z_idx = par_idx;
                        self.right_rotate(z_idx);
                    }
                    // case 3: z is a left child, and z's uncle is black
                    let par_idx = self.at(z_idx).parent?; // can't be nil as it was grandparent
                    let grand_idx = self.at(par_idx).parent?; // can't be nil; must be colored red
                    self.at_mut(par_idx).color = Color::Black;
                    self.at_mut(grand_idx).color = Color::Red;
                    self.left_rotate(grand_idx);
                }
            } else {
                panic!("Z's grandparent reports both of its children as None (insert_fix()).");
            }
        }

        self.enforce_root_black();
        Some(())
    }
    pub fn show(&self)
    where
        K: Display,
        V: Display,
    {
        self.display(Some(self.root));
    }
    pub fn display(&self, root_opt: Option<usize>)
    where
        K: Display,
        V: Display,
    {
        match self.at_opt(root_opt) {
            Some(node) => {
                self.display(node.left);
                println!("{}", node);
                self.display(node.right);
            }
            None => return,
        }
    }
}

impl<K, V> Display for Tree<K, V>
where
    K: Display,
    V: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for n in &self.nodes {
            write!(f, "{}", n)?;
        }
        Ok(())
    }
}
