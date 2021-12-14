

pub mod tree;

#[cfg(test)]
mod tests {
    use crate::tree::Tree;
    #[test]
    fn general() {
        let mut t: Tree<i32, bool> = Tree::new();
        t.insert(0, true);
        println!("");
        t.show();
        t.insert(-1, true);
        println!("");
        t.show();
        t.insert(1, false);
        println!("");
        t.show();
        t.insert(4, true);
        println!("");
        t.show();
        // ! After inserting 4->true, we should have node 1 being black.
        t.insert(3, true);
        println!("");
        t.show();
        t.insert(5, true);
        println!("");
        t.show();
        t.insert(7, false);
        println!("");
        t.show();
        t.insert(2, true);
        println!("");
        t.show();
        t.insert(-3, true);
        t.insert(-10, false);
        t.insert(10, false);
        println!("");
        t.show();
    }
}
