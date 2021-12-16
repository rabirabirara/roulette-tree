use std::cmp::{Ord, Ordering};
use std::fmt::{Display, Formatter};

use crate::node::{Color, Node};

// * The implementation of this RB tree does not actually delete nodes.  It instead leaks them.
// * This tree is best used when you need to insert and update objects, but not remove them - for example, storing a map.

// Why use a Vec over pointers and heap allocation?  Well, pointers (dynamic object creation) are less performant and heap allocation struggles to exploit the cache.  We might lose the ability to deallocate individual elements, but we gain the ability of a fast linear search (which excels for small trees), instant indexing of the tree, a quick determination of length, etc.
// Read https://doc.rust-lang.org/std/collections/struct.BTreeMap.html for more information.

use std::fmt::Debug;
pub struct VecTree<K, V> {
    // ? A node can be allocated or "leaked".
    nodes: Vec<Option<Node<K, V>>>,
    // Store the index of leaked nodes.
    leaked: Vec<usize>,
    root: Option<usize>,
}

impl<K, V> VecTree<K, V>
where
    K: Ord + Display + Debug,
    V: Display + Debug,
{
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            leaked: Vec::new(),
            root: None,
        }
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    // Should be a fast way to access a node at some index.
    fn at(&self, idx: usize) -> &Node<K, V> {
        self.nodes[idx].as_ref().expect(format!("Expected an allocated Some(node) at index {}", idx).as_str())
    }
    fn at_mut(&mut self, idx: usize) -> &mut Node<K, V> {
        self.nodes[idx].as_mut().expect(format!("Expected an allocated Some(node) at index {}", idx).as_str())
    }
    fn try_at(&self, idx: usize) -> Option<&Node<K, V>> {
        self.nodes[idx].as_ref()
    }
    fn try_at_mut(&mut self, idx: usize) -> Option<&mut Node<K, V>> {
        self.nodes[idx].as_mut()
    }
    fn at_opt(&self, idx_opt: Option<usize>) -> Option<&Node<K, V>> {
        match idx_opt {
            Some(idx) => self.try_at(idx),
            _ => None,
        }
    }
    fn at_mut_opt(&mut self, idx_opt: Option<usize>) -> Option<&mut Node<K, V>> {
        match idx_opt {
            Some(idx) => self.try_at_mut(idx),
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
                if par_node.left.contains(&x_idx) {
                    par_node.left.replace(y_idx);
                } else if par_node.right.contains(&x_idx) {
                    par_node.right.replace(y_idx);
                } else {
                    panic!("X's parent does not record X as one of its children in left_rotate().");
                }
            } else {
                // x points to a parent, but it apparently doesn't exist in the tree. error.
                panic!("X points to a parent that is supposedly not in the tree.");
            }
        } else {
            // this subtree is actually the root tree. update the root to y.
            self.root.replace(y_idx);
        }

        let x = self.try_at_mut(x_idx)?;
        x.left = a;
        x.right = b;
        x.parent.replace(y_idx);
        let y = self.try_at_mut(y_idx)?;
        y.left.replace(x_idx);
        y.parent = parent;

        // If b is a subtree, switch its parent between x and y.
        if let Some(b_node) = self.at_mut_opt(b) {
            b_node.parent.replace(x_idx);
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
                if par_node.left.contains(&y_idx) {
                    par_node.left.replace(x_idx);
                } else if par_node.right.contains(&y_idx) {
                    par_node.right.replace(x_idx);
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
            self.root.replace(x_idx);
        }

        let y = self.try_at_mut(y_idx)?;
        y.left = b;
        y.right = c;
        y.parent.replace(x_idx);
        let x = self.try_at_mut(x_idx)?;
        x.right.replace(y_idx);
        x.parent = parent;

        // If b is a subtree, switch its parent between x and y.
        if let Some(b_node) = self.at_mut_opt(b) {
            b_node.parent.replace(y_idx);
        }

        Some(())
    }
    fn enforce_root_black(&mut self) {
        if let Some(root) = self.root {
            self.at_mut(root).color = Color::Black;
        }
    }
    fn minimum(&self, root_opt: Option<usize>) -> Option<usize> {
        let cur_opt = self.at_opt(root_opt);
        if let Some(cur) = cur_opt {
            if let Some(left) = cur.left {
                self.minimum(Some(left))
            } else {
                Some(cur.index)
            }
        } else {
            None
        }
    }
    // Two ways of searching a Vec-BTree: linear, and BST search.
    // Linear is faster in practice thanks to cache locality.
    // BST is faster asymptotically.
    // We implement get() and lookup() to represent both.
    pub fn get(&self, key: &K) -> Option<&V> {
        for k in &self.nodes {
            if let Some(k) = k {
                if k.key.cmp(key) == Ordering::Equal {
                    return Some(&k.value);
                }
            } // else, the node is deallocated; skip it
        }
        return None;
    }
    // get_mut...
    // * Takes ownership of a node, deallocating it
    fn get_and_take_node(&mut self, key: &K) -> Option<Node<K, V>> {
        for k_node in &mut self.nodes {
            if let Some(k) = k_node {
                if k.key.cmp(key) == Ordering::Equal {
                    // ! Check if this causes the node to be deallocated.
                    return std::mem::take(k_node);
                }
            }
        }
        return None;
    }
    pub fn lookup(&self, key: &K) -> Option<&V> {
        let mut cur = self.root;
        while let Some(index) = cur {
            if let Some(n) = self.nodes.get(index) {
                if let Some(node) = n {
                    match node.key.cmp(key) {
                        Ordering::Less => cur = node.right,   // node < key
                        Ordering::Greater => cur = node.left, // key < node
                        Ordering::Equal => return Some(&node.value),
                    }
                } else {
                    panic!("Some index followed by 'pointer' led to a deallocated node in lookup(). index: {}", index);
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
        let mut cur = self.root;

        while let Some(index) = cur {
            if let Some(node_opt) = self.nodes.get_mut(index) {
                if let Some(node) = node_opt {
                    prev = cur;
                    match node.key.cmp(&k) {
                        Ordering::Less => cur = node.right,   // node < key
                        Ordering::Greater => cur = node.left, // key < node
                        Ordering::Equal => return Some(std::mem::replace(&mut node.value, v)),
                    }
                } else {
                    panic!("Some index followed by 'pointer' led to a deallocated node in insert(). index: {}", index);
                }
            } else {
                // Root is not present; add in new root.
                if !self.is_empty() {
                    panic!("could not find node of root index, despite self being occupied.");
                }
                // * If the tree is empty, the next node to be added should be at the start of the array.
                self.root.replace(0);
                self.nodes
                    .push(Some(Node::from(0, None, None, None, k, v, Color::Black)));
                return None;
            }
        }
        // reached nil, tree not empty, prev = Some(node) under which to place the new node.
        let index = self.nodes.len();
        let leaf = self.at_mut(
            prev.expect("ERR: prev should contain a Some(index) that points to an existing node."),
        );

        match k.cmp(&leaf.key) {
            Ordering::Less => { leaf.left.replace(index); },
            Ordering::Greater => { leaf.right.replace(index); },
            Ordering::Equal => unreachable!(),
        }
        let z = Node::from(index, prev, None, None, k, v, Color::Red);
        self.nodes.push(Some(z));
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

            if grand_left.contains(&par_idx) {
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
                    if parent.right.contains(&z_idx) {
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
            } else if grand_right.contains(&par_idx) {
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
                    if parent.left.contains(&z_idx) {
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
    pub fn remove(&mut self, k: K) -> Option<V> 
    where
        V: Default,
    {
        let node = self.get_and_take_node(&k)?;
        let old = node.value;
        let z_idx = node.index;
        self.delete(z_idx);
        Some(old)
    }
    // Replace node u with node v.  v can be nil, u cannot.
    // Note: we don't do any checking for whether or not these indices point to nodes.
    fn transplant(&mut self, u_opt: Option<usize>, v_opt: Option<usize>) {
        let u = self.at_opt(u_opt).expect("u cannot be nil in transplant()!");
        let u_idx = u_opt.expect("u cannot be nil in transplant().");
        let u_parent = u.parent;

        if let Some(v) = self.at_mut_opt(v_opt) {
            v.parent = u_parent;
        }

        match u_parent {
            // static analysis notes that reference to u dies here, and so a mmutable reference can be had.
            Some(p) => {
                if let Some(parent) = self.try_at_mut(p) {
                    if parent.left.contains(&u_idx) {
                        parent.left = v_opt;
                    } else if parent.right.contains(&u_idx) {
                        parent.right = v_opt;
                    } else {
                        panic!("Parent of u did not record having u as child.");
                    }
                } else {
                    panic!("Parent of u not found in the tree.");
                }
            }
            None => self.root = v_opt,
        }
    }
    fn delete(&mut self, z_idx: usize) -> Option<()> {
        
        Some(())
    }
    pub fn show(&self)
    where
        K: Display,
        V: Display,
    {
        self.display(self.root, "");
    }
    pub fn display(&self, root_opt: Option<usize>, tab: &str)
    where
        K: Display,
        V: Display,
    {
        match self.at_opt(root_opt) {
            Some(node) => {
                let tabbed = format!("{}    ", tab);
                self.display(node.left, &tabbed);
                println!("{}{}", tab, node);
                self.display(node.right, &tabbed);
            }
            None => return,
        }
    }
}

impl<K, V> Display for VecTree<K, V>
where
    K: Display,
    V: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for n in &self.nodes {
            if let Some(n) = n {
                write!(f, "{}", n)?;
            }
        }
        Ok(())
    }
}
