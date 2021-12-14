use std::fmt;

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone)]
pub struct Node<K, V> {
    pub index: usize,
    pub parent: Option<usize>,
    pub left: Option<usize>,
    pub right: Option<usize>,
    pub key: K,
    pub value: V,
    pub color: Color,
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

impl<K, V> fmt::Display for Node<K, V>
where
    K: fmt::Display,
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{:?} -> {} -> ({:?}, {:?})]::{:?} ({} -> {})",
            self.parent, self.index, self.left, self.right, self.color, self.key, self.value
        )
    }
}