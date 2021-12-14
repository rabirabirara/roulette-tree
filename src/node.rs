
#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone)]
pub struct Node<K, V> {
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