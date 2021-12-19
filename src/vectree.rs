use std::cmp::{Ord, Ordering};
use std::fmt::{Display, Formatter};

use crate::node::{Color, Node};

// * The implementation of this RB tree does not actually delete nodes.  It instead leaks them.
// * This tree is best used when you need to insert and update objects, but not remove them - for example, storing a map.
// * Of course, the implementation reuses unoccupied spaces in the Vec.  And removing from a Vec, properly, doesn't exactly shrink it either.

// Why use a Vec over pointers and heap allocation?  Well, pointers (dynamic object creation) are less performant and heap allocation struggles to exploit the cache.  We might lose the ability to deallocate individual elements, but we gain the ability of a fast linear search (which excels for small trees), instant indexing of the tree, a quick determination of length, etc.
// Read https://doc.rust-lang.org/std/collections/struct.BTreeMap.html for more information.

const INITIAL_ROOT: usize = 0;

use std::fmt::Debug;
pub struct VecTree<K, V> {
    // ? A node can be allocated or "leaked".
    nodes: Vec<Option<Node<K, V>>>,
    // Store the index of leaked nodes.
    leaked: Vec<usize>,
    root: Option<usize>,
    len: usize,
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
            len: 0,
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    fn clear(&mut self) {
        self.nodes.clear();
        self.leaked.clear();
        self.root = None;
        self.len = 0;
    }
    // Returns number of allocated nodes.
    pub fn len(&self) -> usize {
        self.len
    }
    // Returns number of nodes, allocated + leaked, in the Vec.
    pub fn capacity(&self) -> usize {
        self.nodes.len()
    }
    fn is_root(&self, node: &Node<K, V>) -> bool {
        self.root.contains(&node.index)
    }
    fn set_root(&mut self, root: Option<usize>) {
        self.root = root;
    }
    // Should be a fast way to access a node at some index.
    fn at(&self, idx: usize) -> &Node<K, V> {
        self.nodes[idx]
            .as_ref()
            .expect(format!("Expected an allocated Some(node) at index {}", idx).as_str())
    }
    fn at_mut(&mut self, idx: usize) -> &mut Node<K, V> {
        self.nodes[idx]
            .as_mut()
            .expect(format!("Expected an allocated Some(node) at index {}", idx).as_str())
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
        None
    }
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        for k in &mut self.nodes {
            if let Some(k) = k {
                if k.key.cmp(key) == Ordering::Equal {
                    return Some(&mut k.value);
                }
            } // else, the node is deallocated; skip it
        }
        None
    }
    // * Takes ownership of a node, replacing it with None.  Does this deallocate?
    // See: https://stackoverflow.com/questions/56522510/does-setting-an-option-instance-from-some-to-none-trigger-dropping-of-the-inner
    fn get_node(&self, key: &K) -> Option<&Node<K, V>> {
        for k_node in &self.nodes {
            if let Some(k) = k_node {
                if k.key.cmp(key) == Ordering::Equal {
                    return Some(k);
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
    fn add(&mut self, n: Node<K, V>, i: usize, push: bool) {
        self.len += 1;

        if push {
            self.nodes.push(Some(n));
        } else {
            // at nodes[i] is a deallocated None node; replace it with a Some(n)
            self.nodes[i].replace(n);
        }
    }
    // lookup_mut...
    // Note: maps use "mem::replace" to replace elements.
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let mut prev = None;
        let mut cur = self.root;

        // If the tree is empty, the next node to be added should be at the start of the array.
        // If the tree is empty but has capacity because of deletions and leakage, clear the vec.
        // ? When to clear the inner Vec?  on the last deletion, or on the next insertion?  It'll clear on drop anyway...
        if self.is_empty() {
            self.clear();
            self.root.replace(INITIAL_ROOT);
            self.add(Node::from(INITIAL_ROOT, None, None, None, k, v, Color::Black), 0, true);
            return None;
        }

        // Else, the tree has some elements.
        while let Some(index) = cur {
            // ! This doesn't use .get(), so bounds-checking has been removed, essentially.  Let it panic.
            if let Some(node) = self.nodes.get_mut(index) {
                if let Some(node) = node.as_mut() {
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
                // Index is out of bounds.
                panic!(
                    "The tree is nonempty, but an index was out of bounds: {}",
                    index
                );
            }
        }
        // reached nil, tree not empty, prev = Some(node) under which to place the new node.

        // If there's leaked nodes, place this node in a leaked index. Else place this node at the end.
        // Think of leakage as a Dyck path, where removals raise the path and insertions (after removals) bring it down.  The height of the path is the quantity of leakage.
        // ? Which order to pop from?  Which is more common - removing recently inserted nodes or removing old nodes?
        // ? Does it matter if I reuse nodes by taking from front or from back?
        let push_this;
        let index = if let Some(top) = self.leaked.pop() {
            push_this = false;
            top
        } else {
            push_this = true;
            self.nodes.len()
        };
        
        let leaf = self.at_mut(
            prev.expect("ERR: prev should contain a Some(index) that points to an existing node."),
        );

        match k.cmp(&leaf.key) {
            Ordering::Less => {
                leaf.left.replace(index);
            }
            Ordering::Greater => {
                leaf.right.replace(index);
            }
            Ordering::Equal => unreachable!(),
        }
        self.add(Node::from(index, prev, None, None, k, v, Color::Red), index, push_this);
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
    // Add the index of a node that is leaked.
    fn mark_leaked(&mut self, idx: usize) -> Option<Node<K, V>> {
        self.leaked.push(idx);
        std::mem::take(self.nodes.get_mut(idx)?)
    }
    // Went through a lot of changes just to retain the ability to move out and return the removed value!
    pub fn remove(&mut self, k: K) -> Option<V> {
        let node_idx = self.get_node(&k)?.index;
        self.len -= 1; // if the node is in the tree it will be deleted or we panic.  if not in the tree above will propagate none
        let idx = self
            .delete(node_idx)
            .expect("delete returned None, when there is no situation in which it should not.");
        Some(
            self.mark_leaked(idx)
                .expect(format!("leak() could not get_mut() at {}", idx).as_ref())
                .value,
        )
    }
    // Replace node u with node v.  v can be nil, u cannot.
    // Note: we don't do any checking for whether or not these indices point to nodes.
    fn transplant(&mut self, u_idx: usize, v_opt: Option<usize>) {
        let u = self.try_at(u_idx).expect(
            "Expected u_idx to not point to a deallocated node, but got a None in transplant().",
        );
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
            None => self.set_root(v_opt),
        }
    }
    // Return the index of the node to be leaked.
    fn delete(&mut self, z_idx: usize) -> Option<usize> {
        let x_ptr;
        // let z = self.at(z);
        // let z_left = z.right;
        // * Original color of the deleted node.  If z has two children, then the actual deleted node is y, the minimum of the subtree at z.  y takes z's place and color, but we lose y's original color; hence.
        let z = self.at(z_idx);
        let z_left = z.left;
        let z_right = z.right;
        let z_color = z.color;
        let mut original_color = z_color;

        if z_left.is_none() {
            // case 1: z has no left child, so replace z with right child (and tree)
            x_ptr = z_right;
            self.transplant(z_idx, z_right);
        } else if z_right.is_none() {
            // case 2: z has no right child (but has a left child), so replace z with left child (and tree)
            x_ptr = z_left;
            self.transplant(z_idx, z_left);
        } else {
            // z has two children.  there are now new cases.
            let y_idx = self.minimum(z_right)?; // guaranteed to be some by if branch
            let y = self.at(y_idx);
            let y_right = y.right;
            original_color = y.color;
            x_ptr = y.right;
            if y.parent.contains(&z_idx) {
                // case 3: z's right child has no left subtree. then replace z with right child and call it a day.
                // also: x's parent is ALREADY y. x is the right child of y, and y is the right child of z.
            } else {
                // TODO: verify this logic is correct.  Maybe think about using split_at_mut?  After all parent and child cannot be same node.
                // case 4: z's right child has a left subtree. y = minimum of z.right subtree.
                // Delete y and replace it with it's right child.
                self.transplant(y_idx, y_right);
                let y = self.at_mut(y_idx);
                y.right = z_right;
                let y_right = self.at_mut(z_right?);
                y_right.parent.replace(y_idx);
            }
            self.transplant(z_idx, Some(y_idx));
            let y = self.at_mut(y_idx);
            y.left = z_left;
            y.color = z_color;
            let y_left = self.at_mut(z_left?);
            y_left.parent.replace(y_idx);
        }

        if original_color == Color::Black {
            self.delete_fix(x_ptr);
        }

        Some(z_idx)
    }
    fn delete_fix(&mut self, replaced_opt: Option<usize>) -> Option<()> {
        // we could have transplanted a null node, so leave that option open. (happens only after deletes, because usually leaves aren't black.)
        // in that case, a leaf node was deleted, and replaced with null, which is black.  so no changes need to be made.
        let mut x_opt = replaced_opt;

        // x is only assigned to x.p in this loop, and since x is never root, x.p must exist.
        // if x is null, then replaced_opt was a leaf node (z had no children).
        while let Some(x) = self.at_opt(x_opt) {
            if self.is_root(x) || x.color == Color::Red {
                // if x is red, color it black (outside the loop).
                break;
            }

            // ! Apparently w's children should exist? w should exist by property 5.
            let x_parent_idx = x.parent?;

            if x_opt == self.at(x_parent_idx).left {
                let mut w_idx = self.at(x_parent_idx).right?;

                // Case 1: x's sibling w is red
                if self.at(w_idx).color == Color::Red {
                    self.at_mut(w_idx).color = Color::Black;
                    self.at_mut(x_parent_idx).color = Color::Red;
                    self.left_rotate(x_parent_idx);
                    w_idx = self.at(x_parent_idx).right?;
                }

                let w = self.at(w_idx);
                let w_left = w.left;
                let w_right = w.right;
                let w_left_black = self.has_color(w_left, Color::Black);
                let w_right_black = self.has_color(w_right, Color::Black);

                if w_left_black && w_right_black {
                    // Case 2: w has two black children
                    self.at_mut(w_idx).color = Color::Black;
                    x_opt.replace(x_parent_idx);
                } else {
                    // case 3
                    if w_right_black {
                        self.at_mut(w_left?).color = Color::Black;
                        self.at_mut(w_idx).color = Color::Red;
                        self.right_rotate(w_idx); // mutates x.parent
                        w_idx = self.at(x_parent_idx).right?; // * we do a lot of reassigning...
                    }
                    // case 4:
                    self.at_mut(w_idx).color = self.at(x_parent_idx).color;
                    self.at_mut(x_parent_idx).color = Color::Black;
                    self.at_mut(w_right?).color = Color::Black;
                    self.left_rotate(x_parent_idx);
                    break;
                }
            } else if x_opt == self.at(x_parent_idx).right {
                let mut w_idx = self.at(x_parent_idx).left?;

                // Case 1: x's sibling w is red
                if self.at(w_idx).color == Color::Red {
                    self.at_mut(w_idx).color = Color::Black;
                    self.at_mut(x_parent_idx).color = Color::Red;
                    self.right_rotate(x_parent_idx);
                    w_idx = self.at(x_parent_idx).left?;
                }

                let w = self.at(w_idx);
                let w_left = w.left;
                let w_right = w.right;
                let w_left_black = self.has_color(w_left, Color::Black);
                let w_right_black = self.has_color(w_right, Color::Black);

                if w_left_black && w_right_black {
                    // Case 2: w has two black children
                    self.at_mut(w_idx).color = Color::Black;
                    x_opt.replace(x_parent_idx);
                } else {
                    // case 3
                    if w_left_black {
                        self.at_mut(w_right?).color = Color::Black;
                        self.at_mut(w_idx).color = Color::Red;
                        self.left_rotate(w_idx); // mutates x.parent
                        w_idx = self.at(x_parent_idx).left?; // * we do a lot of reassigning...
                    }
                    // case 4:
                    self.at_mut(w_idx).color = self.at(x_parent_idx).color;
                    self.at_mut(x_parent_idx).color = Color::Black;
                    self.at_mut(w_left?).color = Color::Black;
                    self.right_rotate(x_parent_idx);
                    break;
                }
            }
        }

        // Set x to black.  It may seem like you only leave the loop if x is the root or is already black, but that's only in pseudocode.  You have a lot of breaks in the loop, remember?
        // Also, x_opt is occasionally None, because a z with two children, the one on the right y, might have no child x, and so x is None.
        if let Some(x) = self.at_mut_opt(x_opt) {
            x.color = Color::Black;
        }
        Some(())
    }
    fn has_color(&self, idx_opt: Option<usize>, color: Color) -> bool {
        // If the idx_opt is null, then its color is actually black.
        match idx_opt {
            Some(idx) => match self.try_at(idx) {
                Some(n) => n.color == color,
                None => false,
            },
            None => match color {
                Color::Red => false,
                Color::Black => true,
            },
        }
    }
    pub fn show(&self)
    where
        K: Display,
        V: Display,
    {
        self.display(self.root, "", 0);
    }
    pub fn display(&self, root_opt: Option<usize>, tab: &str, depth: usize)
    where
        K: Display,
        V: Display,
    {
        match self.at_opt(root_opt) {
            Some(node) => {
                let tabbed = format!("{}    ", tab);
                self.display(node.left, &tabbed, depth + 1);
                println!("{}{}{}", tab, depth, node);
                self.display(node.right, &tabbed, depth + 1);
            }
            None => println!("{}None", tab),
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
