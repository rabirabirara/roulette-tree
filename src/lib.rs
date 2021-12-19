#![feature(option_result_contains)]


pub mod vectree;
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
    #[test]
    fn removal_1() {
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
        t.remove(0);
        println!();
        t.show();
    }
    #[test]
    fn removal_2() {
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
        t.remove(0);
        t.remove(-1);
        t.remove(1);
        t.remove(4);
        t.remove(3);
        t.remove(5);
        println!();
        t.show();
        // t.remove(7);
        // t.remove(2);
        // t.remove(-3);
        // t.remove(-10);
        // t.remove(10);
    }
}
