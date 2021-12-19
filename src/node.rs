use std::fmt;

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum Color {
    Red,
    Black,
}

impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Color::Red => write!(f, "R"),
            Color::Black => write!(f, "B"),
        }
    }
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
        k: K,
        v: V,
        color: Color,
    ) -> Self {
        Node {
            index,
            parent,
            left,
            right,
            key: k,
            value: v,
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
            // "[{:?} -> {} -> ({:?}, {:?})]-{:?} ({} -> {})",
            // self.parent, self.index, self.left, self.right, self.color, self.key, self.value
            "[{} -> {} : {}.{}]",
            self.key, self.value, self.index, self.color
        )
    }
}