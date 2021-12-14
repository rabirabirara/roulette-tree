#![feature(option_result_contains)]


pub mod vectree;
pub mod boxtree;
mod node;

// read: https://doc.rust-lang.org/reference/visibility-and-privacy.html
// use mod to make a module available from a point, but only export public functions/structs.
// use pub mod to export outwardly all public functions/structs.

#[cfg(test)]
mod tests {
    use crate::vectree::VecTree;
    #[test]
    fn general() {
        let mut t: VecTree<i32, bool> = VecTree::new();
        t.insert(0, true);
        t.insert(-1, true);
        t.insert(1, false);
        t.insert(4, true);
        t.insert(3, true);
        t.insert(5, true);
        t.insert(7, false);
        t.insert(2, true);
        t.insert(-3, true);
        t.insert(-10, false);
        t.insert(10, false);
        t.show();
    }
}
