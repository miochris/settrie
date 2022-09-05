// #![feature(const_fn_trait_bound)]
#![feature(const_btree_new)]
//! A set-trie data structure for fast superset/subset retrieval.
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};
use std::fmt::{Debug, Display};
use std::hash::Hash;

/// A node is an element in the set-trie.
#[derive(Debug, Clone)]
struct Node<K>
where
    K: Ord + Clone + Copy,
{
    val: K,
    children: BTreeMap<K, Node<K>>,
    leaf_size: usize,
    leaf_set: Option<Vec<K>>, // leaf_nodes use this to store the full path
}
impl<K> Ord for Node<K>
where
    K: Ord + Clone + Copy,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.val.cmp(&other.val)
    }
}
impl<K> PartialOrd for Node<K>
where
    K: Ord + Clone + Copy,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<K> Eq for Node<K> where K: Ord + Clone + Copy {}
impl<K> PartialEq for Node<K>
where
    K: Ord + Clone + Copy,
{
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}

impl<K> Node<K>
where
    K: Ord + Clone + Copy,
{
    pub const fn new(val: K) -> Self {
        Self {
            val,
            children: BTreeMap::<K, Node<K>>::new(),
            leaf_size: 1,
            leaf_set: None,
        }
    }
    /// insert a new set into set_trie
    ///
    /// exist_prefix: when the set_trie contains a leaf that is a prefix of the set
    pub fn insert_set_to_node(&mut self, set: &[K], pos_in_set: usize, exist_prefix: bool) {
        match set.len().cmp(&pos_in_set) {
            Ordering::Equal => {
                if self.children.is_empty() {
                    self.leaf_set = Some(set.to_vec());
                } else {
                    // already checked supersets before calling this method
                    // it's always zero children when reaching to the end of the set
                    unreachable!();
                }
            }
            Ordering::Greater => {
                let elem = set[pos_in_set];
                match self.children.get_mut(&elem) {
                    // already in
                    Some(child) => {
                        if !exist_prefix {
                            child.leaf_size += 1;
                        }
                        child.insert_set_to_node(set, pos_in_set + 1, exist_prefix);
                    }
                    None => {
                        // clear existing leaf set if stored
                        self.leaf_set = None;
                        // add a new child
                        let child = self.children.entry(elem).or_insert_with(|| Node::new(elem));
                        child.insert_set_to_node(set, pos_in_set + 1, exist_prefix);
                    }
                }
            }
            Ordering::Less => {
                unreachable!();
            }
        }
    }
}

/// A set-trie is a trie, which stores sets.
/// Branches are sorted and child node is always bigger than its parent node.
/// Each node has a leaf_size to indicate how many leaves its children have in total.
/// It's used to speed up the deletion. When leaf_size == 1, there is no need to go down the route for deletion.
/// Each leaf has a leaf_set to store the route from the top to this node. This is used to get all sets this trie stores.
///
#[derive(Clone, Debug, Default)]
pub struct SetTrie<K>
where
    K: Ord + Clone + Copy,
{
    branches: BTreeMap<K, Node<K>>,
}

#[allow(dead_code)]
impl<K> SetTrie<K>
where
    K: Ord + Clone + Copy + Display + Debug + Hash,
{
    #[must_use]
    pub const fn new() -> Self {
        Self {
            branches: BTreeMap::<K, Node<K>>::new(),
        }
    }

    /// returns true if a superset or the same set exists
    pub fn exist_superset(&self, set: &[K]) -> bool {
        if set.is_empty() {
            return true;
        }
        self.branches
            .iter()
            .any(|(_k, v)| self.exist_superset_in_node(v, set, 0))
    }

    fn exist_superset_in_node(&self, node: &Node<K>, set: &[K], pos_in_set: usize) -> bool {
        if pos_in_set == set.len() {
            return true;
        }
        let node_val = node.val;
        let set_val = set[pos_in_set];
        match node_val.cmp(&set_val) {
            Ordering::Equal => {
                if pos_in_set == set.len() - 1 {
                    true
                } else {
                    node.children
                        .iter()
                        .filter(|(k, &_)| **k <= set[pos_in_set + 1])
                        .any(|(_k, v)| self.exist_superset_in_node(v, set, pos_in_set + 1))
                }
            }
            Ordering::Less => node
                .children
                .iter()
                .filter(|(k, _v)| **k <= set[pos_in_set])
                .any(|(_k, v)| self.exist_superset_in_node(v, set, pos_in_set)),
            Ordering::Greater => false,
        }
    }

    /// returns all sets stored in the set-trie
    pub fn get_all_supersets(&self) -> Vec<Vec<K>> {
        return self
            .branches
            .iter()
            .map(|(_k, branch)| self.get_all_leaf_sets(branch))
            .flatten()
            .collect();
    }

    /// get all supersets of one set
    pub fn get_supersets(&self, set: &[K]) -> Vec<Vec<K>> {
        assert!(!set.is_empty());

        self.branches
            .iter()
            .filter(|(k, _v)| **k <= set[0])
            .map(|(_k, branch)| self.get_supersets_from_node(branch, set, 0))
            .flatten()
            .collect()
    }

    /// returns all leaf_sets from the node or the node's children
    fn get_all_leaf_sets(&self, node: &Node<K>) -> Vec<Vec<K>> {
        match node.children.len() {
            0 => {
                vec![node
                    .leaf_set
                    .as_ref()
                    .unwrap_or_else(|| panic!("node {:?} with no child should have leaf_set", node))
                    .clone()]
            }
            _ => node
                .children
                .iter()
                .map(|(_k, v)| self.get_all_leaf_sets(v))
                .flatten()
                .collect(),
        }
    }

    /// returns supersets of a set from the node's leaf_sets
    fn get_supersets_from_node(&self, node: &Node<K>, set: &[K], pos_in_set: usize) -> Vec<Vec<K>> {
        let len = set.len();
        let is_last = pos_in_set == len - 1;
        let target = set[pos_in_set];
        let node_val = node.val;

        match node_val.cmp(&target) {
            Ordering::Equal => {
                if is_last {
                    self.get_all_leaf_sets(node)
                } else {
                    let new_target = set[pos_in_set + 1];
                    // go to children
                    return node
                        .children
                        .iter()
                        .filter(|(k, _v)| **k <= new_target)
                        .map(|(_k, v)| self.get_supersets_from_node(v, set, pos_in_set + 1))
                        .flatten()
                        .collect::<Vec<Vec<K>>>();
                }
            }
            Ordering::Less => {
                // go to children
                return node
                    .children
                    .iter()
                    .filter(|(k, _v)| **k <= target)
                    .map(|(_k, v)| self.get_supersets_from_node(v, set, pos_in_set))
                    .flatten()
                    .collect::<Vec<Vec<K>>>();
            }
            Ordering::Greater => Vec::new(),
        }
    }

    /// checks if a prefix of the set is a leaf_set of the set_trie
    ///
    /// it is used to decide whether to update leaf_size or not when inserting a new set
    fn exist_prefix(&self, set: &[K]) -> bool {
        match self.branches.get(&set[0]) {
            None => false,
            Some(node) => {
                if node.children.is_empty() {
                    if set.len() == 1 {
                        // both set and set_trie has a set with the size of 1
                        // exist_superset() would return true and the code won't reach here
                        unreachable!();
                    } else {
                        true
                    }
                } else if set.len() == 1 {
                    false
                } else {
                    self.crawl(node, &set[1..])
                }
            }
        }
    }

    /// keep going down the trie to check if a leaf-set equals to a prefix of the set
    fn crawl(&self, node: &Node<K>, set: &[K]) -> bool {
        match node.children.len() {
            0 => true,
            _ => match node.children.get(&set[0]) {
                None => false,
                Some(child) => {
                    if set.len() == 1 {
                        unreachable!();
                    } else {
                        self.crawl(child, &set[1..])
                    }
                }
            },
        }
    }

    /// check if the set_trie contains a leaf_set which is a subset of the given set
    pub fn exist_subset(&self, set: &[K]) -> bool {
        let s = set.iter().collect::<HashSet<_>>();
        return self
            .branches
            .iter()
            .any(|(_k, node)| self.exist_subset_in_node(node, &s));
    }

    /// returns leaf_sets which are subsets of the given set
    pub fn get_subsets(&self, set: &[K]) -> Vec<Vec<K>> {
        let s = set.iter().collect::<HashSet<_>>();
        return self
            .branches
            .iter()
            .map(|(_k, node)| self.get_subset_from_node(node, &s))
            .flatten()
            .collect();
    }

    /// returns leaf_sets of the node which are subsets of the given set
    fn get_subset_from_node(&self, node: &Node<K>, set: &HashSet<&K>) -> Vec<Vec<K>> {
        if set.contains(&node.val) {
            match node.children.len() {
                0 => {
                    let r = node.leaf_set.clone().unwrap();
                    return vec![r];
                }
                _ => node
                    .children
                    .iter()
                    .map(|(_k, child)| self.get_subset_from_node(child, set))
                    .flatten()
                    .collect(),
            }
        } else {
            Vec::new()
        }
    }

    /// check if any of the node's leaf-sets is a subset of the given set
    fn exist_subset_in_node(&self, node: &Node<K>, set: &HashSet<&K>) -> bool {
        if set.contains(&node.val) {
            match node.children.len() {
                0 => true,
                _ => node
                    .children
                    .iter()
                    .any(|(_k, child)| self.exist_subset_in_node(child, set)),
            }
        } else {
            false
        }
    }

    /// insert a set into the set-trie, it will do nothing if a superset exists
    pub fn insert_set(&mut self, set: &[K]) -> bool {
        if self.exist_superset(set) {
            false
        } else {
            self.insert_new_set(set);
            true
        }
    }

    /// insert a new set, it assumes the set doesn't exist in the set-trie and there is no leaf-set
    /// which is a subset of the set to be inserted
    pub fn insert_new_set(&mut self, set: &[K]) {
        assert!(!set.is_empty());

        // used to not to increase leaf_size when extending an existing node
        let exist_prefix = self.exist_prefix(set);

        let elem = set[0];
        match self.branches.get_mut(&elem) {
            Some(node) => {
                if !exist_prefix {
                    node.leaf_size += 1;
                }
            }
            None => {
                self.branches.insert(elem, Node::new(set[0]));
            }
        }
        let node = self.branches.get_mut(&elem).unwrap();
        node.insert_set_to_node(set, 1, exist_prefix);
    }

    /// delete an existing set from the set-trie
    pub fn del_set_wo_checking(&mut self, set: &[K]) {
        let mut node = self.branches.get_mut(&set[0]).unwrap();
        match set.len() {
            1 => {
                self.branches.remove(&set[0]);
            }
            2 => match node.leaf_size {
                1 => {
                    self.branches.remove(&set[0]);
                }
                _ => {
                    node.leaf_size -= 1;
                    node.children.remove(&set[1]);
                }
            },
            _ => match node.leaf_size {
                1 => {
                    self.branches.remove(&set[0]);
                }
                _ => {
                    for (i, _k) in set.iter().enumerate() {
                        let child = node.children.get(&set[i + 1]).unwrap();
                        match child.leaf_size {
                            1 => {
                                node.leaf_size -= 1;
                                node.children.remove(&set[i + 1]);
                                break;
                            }
                            _ => {
                                node.leaf_size -= 1;
                            }
                        }
                        node = node.children.get_mut(&set[i + 1]).unwrap();
                    }
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_all_supersets() {
        let mut set_trie = SetTrie::new();
        let supersets = set_trie.get_all_supersets();
        let empty_vec: Vec<Vec<i32>> = Vec::new();
        assert_eq!(supersets, empty_vec);
        set_trie.insert_set(&[1]);
        let supersets = set_trie.get_all_supersets();
        assert_eq!(supersets, vec![vec![1]]);
        set_trie.insert_set(&[2]);
        let supersets = set_trie.get_all_supersets();
        assert_eq!(supersets, vec![vec![1], vec![2]]);

        set_trie.insert_set(&[1, 3]);
        let supersets = set_trie.get_all_supersets();
        assert_eq!(supersets, vec![vec![1, 3], vec![2]]);
    }

    #[test]
    fn test_get_supersets() {
        let mut set_trie = SetTrie::new();
        set_trie.insert_set(&[1]);
        let supersets = set_trie.get_supersets(&[1]);
        assert_eq!(supersets, [vec![1]]);
        let set1 = vec![1, 2, 3];
        set_trie.insert_new_set(&set1);
        let set2 = vec![1, 2, 4];
        set_trie.insert_new_set(&set2);
        let supersets = set_trie.get_supersets(&[1]);
        assert_eq!(supersets, [set1.clone(), set2.clone()]);
        let supersets = set_trie.get_supersets(&[2, 4]);
        assert_eq!(supersets, [set2.clone()]);
        let supersets = set_trie.get_supersets(&[4]);
        assert_eq!(supersets, [set2.clone()]);
        let set3 = vec![4, 5];
        set_trie.insert_new_set(&set3);
        let supersets = set_trie.get_supersets(&[4]);
        assert_eq!(supersets, [set2.clone(), set3]);
        let supersets = set_trie.get_supersets(&[1, 2]);
        assert_eq!(supersets, [set1.clone(), set2.clone()]);
        let supersets = set_trie.get_supersets(&[1, 2, 3]);
        assert_eq!(supersets, [set1.clone()]);
        let supersets = set_trie.get_supersets(&[2, 3]);
        assert_eq!(supersets, [set1]);
        let supersets = set_trie.get_supersets(&[1, 4]);
        assert_eq!(supersets, [set2]);
        let supersets = set_trie.get_supersets(&[3, 4]);
        assert_eq!(supersets, Vec::<Vec<i32>>::new());
        let supersets = set_trie.get_supersets(&[2, 3, 4]);
        assert_eq!(supersets, Vec::<Vec<i32>>::new());
        let supersets = set_trie.get_supersets(&[3, 4, 5]);
        assert_eq!(supersets, Vec::<Vec<i32>>::new());
        let supersets = set_trie.get_supersets(&[1, 2, 5]);
        assert_eq!(supersets, Vec::<Vec<i32>>::new());
        let supersets = set_trie.get_supersets(&[1, 4, 5]);
        assert_eq!(supersets, Vec::<Vec<i32>>::new());
    }

    #[test]
    fn test_get_all_leaf_sets() {
        let mut set_trie = SetTrie::new();
        let set1 = vec![1, 2, 3];
        set_trie.insert_new_set(&set1);
        let set2 = vec![1, 2, 4, 5];
        set_trie.insert_new_set(&set2);
        let set3 = vec![6];
        set_trie.insert_new_set(&set3);

        let node_1 = set_trie.branches.get(&1).unwrap();
        let node_2 = node_1.children.get(&2).unwrap();
        let node_3 = node_2.children.get(&3).unwrap();
        let node_4 = node_2.children.get(&4).unwrap();
        let node_5 = node_4.children.get(&5).unwrap();
        let node_6 = set_trie.branches.get(&6).unwrap();

        assert_eq!(node_1.leaf_size, 2);
        assert_eq!(node_2.leaf_size, 2);
        assert_eq!(node_3.leaf_size, 1);
        assert_eq!(node_4.leaf_size, 1);
        assert_eq!(node_5.leaf_size, 1);
        assert_eq!(node_6.leaf_size, 1);

        assert_eq!(
            vec![set1.clone(), set2.clone()],
            set_trie.get_all_leaf_sets(node_1)
        );
        assert_eq!(
            vec![set1.clone(), set2.clone()],
            set_trie.get_all_leaf_sets(node_2)
        );
        assert_eq!(vec![set1], set_trie.get_all_leaf_sets(node_3));
        assert_eq!(vec![set2.clone()], set_trie.get_all_leaf_sets(node_4));
        assert_eq!(vec![set2], set_trie.get_all_leaf_sets(node_5));
        assert_eq!(vec![set3], set_trie.get_all_leaf_sets(node_6));
    }

    #[test]
    fn test_exists_superset() {
        let mut set_trie = SetTrie::new();
        let set1 = &[1, 2, 3, 4];
        set_trie.insert_new_set(set1);
        let set2 = &[1, 2, 3, 5];
        set_trie.insert_new_set(set2);
        let set3 = &[2, 4, 6];
        set_trie.insert_new_set(set3);
        let set4 = &[2, 4, 7];
        set_trie.insert_new_set(set4);
        let set5 = &[5, 6];
        set_trie.insert_new_set(set5);

        assert!(set_trie.exist_superset(&[1, 2]));
        assert!(set_trie.exist_superset(&[1, 3]));
        assert!(set_trie.exist_superset(&[1, 4]));
        assert!(set_trie.exist_superset(&[1, 5]));
        assert!(set_trie.exist_superset(&[1, 2, 4]));
        assert!(set_trie.exist_superset(&[1, 2, 5]));
        assert!(set_trie.exist_superset(&[2, 4]));
        assert!(set_trie.exist_superset(&[2, 6]));
        assert!(set_trie.exist_superset(&[2, 7]));
        assert!(set_trie.exist_superset(&[4, 6]));
        assert!(set_trie.exist_superset(&[4, 7]));
        assert!(set_trie.exist_superset(&[5, 6]));
        assert!(set_trie.exist_superset(&[1, 2, 3, 4]));
        assert!(set_trie.exist_superset(&[1, 2, 3, 5]));

        assert!(!set_trie.exist_superset(&[4, 5]));
        assert!(!set_trie.exist_superset(&[5, 7]));
        assert!(!set_trie.exist_superset(&[1, 7]));
        assert!(!set_trie.exist_superset(&[1, 2, 6]));
        assert!(!set_trie.exist_superset(&[1, 2, 7]));
        assert!(!set_trie.exist_superset(&[1, 5, 6]));
    }

    #[test]
    fn test_get_supersets_from_node() {
        let mut set_trie = SetTrie::new();
        let set1 = vec![1, 2, 4];
        set_trie.insert_new_set(&set1);
        let set2 = vec![1, 2, 3];
        set_trie.insert_new_set(&set2);
        let n1 = set_trie.branches.get(&1).unwrap();
        let ss1 = set_trie.get_supersets_from_node(n1, &[1, 5], 0);
        assert_eq!(ss1.len(), 0);
        let ss2 = set_trie.get_supersets_from_node(n1, &[1], 0);
        assert_eq!(ss2.len(), 2);
        assert_eq!(ss2, vec![[1, 2, 3], [1, 2, 4]]);
        let ss3 = set_trie.get_supersets_from_node(n1, &[1], 0);
        assert_eq!(ss3.len(), 2);
        assert_eq!(ss3, vec![[1, 2, 3], [1, 2, 4]]);
    }

    #[test]
    fn test_get_subsets() {
        let mut set_trie = SetTrie::new();
        let set1 = vec![1, 2, 3];
        set_trie.insert_new_set(&set1);
        let set2 = vec![1, 2, 4];
        set_trie.insert_new_set(&set2);
        let subsets = set_trie.get_subsets(&[1, 2, 3, 4]);
        assert_eq!(subsets, [set1.clone(), set2.clone()]);
        let subsets = set_trie.get_subsets(&[1, 2, 3, 4, 5]);
        assert_eq!(subsets, [set1.clone(), set2.clone()]);
        let set3 = vec![1, 3, 5];
        set_trie.insert_new_set(&set3);
        let set4 = vec![4, 5, 6];
        set_trie.insert_new_set(&set4);
        let set5 = vec![4, 6, 7];
        set_trie.insert_new_set(&set5);
        let set6 = vec![4, 6, 8];
        set_trie.insert_new_set(&set6);

        let subsets = set_trie.get_subsets(&[1, 2, 3, 4, 5]);
        assert_eq!(subsets, [set1, set2, set3.clone()]);
        let subsets = set_trie.get_subsets(&[1, 3, 4, 5, 6, 8]);
        assert_eq!(subsets, [set3, set4, set6]);
    }
    #[test]
    fn test_exist_subset() {
        let mut set_trie = SetTrie::new();
        let set1 = vec![1, 2, 3];
        set_trie.insert_new_set(&set1);
        let set2 = vec![1, 2, 4];
        set_trie.insert_new_set(&set2);
        let exist = set_trie.exist_subset(&[1, 2, 3, 4]);
        assert!(exist);
        let exist = set_trie.exist_subset(&[1, 2, 3, 4, 5]);
        assert!(exist);
        let exist = set_trie.exist_subset(&[2, 4]);
        assert!(!exist);
        let set3 = vec![1, 3, 5];
        set_trie.insert_new_set(&set3);
        let set4 = vec![4, 5, 6];
        set_trie.insert_new_set(&set4);
        let set5 = vec![4, 6, 7];
        set_trie.insert_new_set(&set5);
        let set6 = vec![4, 6, 8];
        set_trie.insert_new_set(&set6);

        let exist = set_trie.exist_subset(&[1, 2, 3, 4, 5]);
        assert!(exist);
        let exist = set_trie.exist_subset(&[1, 3, 4, 5, 6, 8]);
        assert!(exist);
        let exist = set_trie.exist_subset(&[1, 3, 6]);
        assert!(!exist);
        let exist = set_trie.exist_subset(&[1, 4, 6]);
        assert!(!exist);
        let exist = set_trie.exist_subset(&[1, 3, 4]);
        assert!(!exist);
    }

    #[test]
    fn test_exist_prefix() {
        let mut set_trie = SetTrie::new();
        let set1 = vec![1, 2, 3];
        set_trie.insert_new_set(&set1);
        assert!(set_trie.exist_prefix(&[1, 2, 3, 4]));

        let mut set_trie = SetTrie::new();
        let set1 = vec![1];
        set_trie.insert_new_set(&set1);
        assert!(set_trie.exist_prefix(&[1, 2, 3]));

        //
        let mut set_trie = SetTrie::new();
        let set1 = vec![1, 2, 3];
        set_trie.insert_new_set(&set1);
        assert!(!set_trie.exist_prefix(&[1]));
    }
    #[test]
    fn test_leaf_size_1() {
        let mut set_trie = SetTrie::new();
        let set1 = vec![1, 2, 3];
        set_trie.insert_new_set(&set1);
        let set2 = vec![1, 2, 4];
        set_trie.insert_new_set(&set2);

        let node1 = set_trie.branches.get(&1).unwrap();
        assert_eq!(node1.leaf_size, 2);
        let node2 = node1.children.get(&2).unwrap();
        assert_eq!(node2.leaf_size, 2);
        let node3 = node2.children.get(&3).unwrap();
        assert_eq!(node3.leaf_size, 1);
        let node4 = node2.children.get(&4).unwrap();
        assert_eq!(node4.leaf_size, 1);

        set_trie.del_set_wo_checking(&set2);
        let node1 = set_trie.branches.get(&1).unwrap();
        assert_eq!(node1.leaf_size, 1);
    }
    #[test]
    fn test_leaf_size_2() {
        let mut set_trie = SetTrie::new();
        let set1 = vec![1, 2, 3, 5, 6];
        set_trie.insert_new_set(&set1);
        let set2 = vec![1, 2, 3, 7];
        set_trie.insert_new_set(&set2);
        let set3 = vec![1, 2, 4, 5, 6];
        set_trie.insert_new_set(&set3);
        let set4 = vec![1, 2, 4, 7];
        set_trie.insert_new_set(&set4);

        let node1 = set_trie.branches.get(&1).unwrap();
        assert_eq!(node1.leaf_size, 4);
        let node2 = set_trie.branches.get(&1).unwrap().children.get(&2).unwrap();
        assert_eq!(node2.leaf_size, 4);
        let node3 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&3)
            .unwrap();
        assert_eq!(node3.leaf_size, 2);
        let node5_1 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&3)
            .unwrap()
            .children
            .get(&5)
            .unwrap();
        assert_eq!(node5_1.leaf_size, 1);
        let node6_1 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&3)
            .unwrap()
            .children
            .get(&5)
            .unwrap()
            .children
            .get(&6)
            .unwrap();
        assert_eq!(node6_1.leaf_size, 1);
        let node7_1 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&3)
            .unwrap()
            .children
            .get(&7)
            .unwrap();
        assert_eq!(node7_1.leaf_size, 1);

        let node4 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&4)
            .unwrap();
        assert_eq!(node4.leaf_size, 2);
        let node5_2 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&4)
            .unwrap()
            .children
            .get(&5)
            .unwrap();
        assert_eq!(node5_2.leaf_size, 1);
        let node6_2 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&4)
            .unwrap()
            .children
            .get(&5)
            .unwrap()
            .children
            .get(&6)
            .unwrap();
        assert_eq!(node6_2.leaf_size, 1);
        let node7_2 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&4)
            .unwrap()
            .children
            .get(&7)
            .unwrap();
        assert_eq!(node7_2.leaf_size, 1);

        set_trie.del_set_wo_checking(&set3);

        let node1 = set_trie.branches.get(&1).unwrap();
        assert_eq!(node1.leaf_size, 3);
        let node2 = set_trie.branches.get(&1).unwrap().children.get(&2).unwrap();
        assert_eq!(node2.leaf_size, 3);
        let node3 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&3)
            .unwrap();
        assert_eq!(node3.leaf_size, 2);
        let node5_1 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&3)
            .unwrap()
            .children
            .get(&5)
            .unwrap();
        assert_eq!(node5_1.leaf_size, 1);
        let node6_1 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&3)
            .unwrap()
            .children
            .get(&5)
            .unwrap()
            .children
            .get(&6)
            .unwrap();
        assert_eq!(node6_1.leaf_size, 1);
        let node7_1 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&3)
            .unwrap()
            .children
            .get(&7)
            .unwrap();
        assert_eq!(node7_1.leaf_size, 1);

        let node4 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&4)
            .unwrap();
        assert_eq!(node4.leaf_size, 1);
        assert_eq!(node4.children.len(), 1);
        let node7_2 = set_trie
            .branches
            .get(&1)
            .unwrap()
            .children
            .get(&2)
            .unwrap()
            .children
            .get(&4)
            .unwrap()
            .children
            .get(&7)
            .unwrap();
        assert_eq!(node7_2.leaf_size, 1);
    }
    #[test]
    fn test_leaf_size_3() {
        let mut set_trie = SetTrie::new();
        let set1 = &[1];
        set_trie.insert_new_set(set1);
        let set2 = &[1, 2];
        set_trie.insert_new_set(set2);

        let node1 = set_trie.branches.get(&1).unwrap();
        assert_eq!(node1.leaf_size, 1);
        let node2 = node1.children.get(&2).unwrap();
        assert_eq!(node2.leaf_size, 1);
    }
    #[test]
    fn test_del_set_wo_checking_0() {
        let mut set_trie = SetTrie::new();
        let set1 = &[0, 2, 3];
        set_trie.insert_new_set(set1);
        let set2 = &[0, 4];
        set_trie.insert_new_set(set2);
        let set3 = &[1, 2, 3];
        set_trie.insert_new_set(set3);
        let set4 = &[1, 4];
        set_trie.insert_new_set(set4);
        set_trie.del_set_wo_checking(set1);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(all_supersets, vec![vec![0, 4], vec![1, 2, 3], vec![1, 4]]);
    }
    #[test]
    fn test_del_set_wo_checking_1() {
        let mut set_trie = SetTrie::new();
        let set1 = &[1, 2, 3];
        set_trie.insert_new_set(set1);
        let set2 = &[1, 2, 4];
        set_trie.insert_new_set(set2);
        let set3 = &[2, 3, 4];
        set_trie.insert_new_set(set3);
        let set4 = &[2, 5];
        set_trie.insert_new_set(set4);
        set_trie.del_set_wo_checking(set3);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(
            all_supersets,
            vec![vec![1, 2, 3], vec![1, 2, 4], vec![2, 5]]
        );
        let set5 = vec![2, 5, 6];
        set_trie.insert_new_set(&set5);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(
            all_supersets,
            vec![vec![1, 2, 3], vec![1, 2, 4], vec![2, 5, 6]]
        );
    }
    #[test]
    fn test_del_set_wo_checking_2() {
        let mut set_trie = SetTrie::new();
        let set1 = &[1, 2, 3];
        set_trie.insert_new_set(set1);
        let set3 = &[2, 3, 4];
        set_trie.insert_new_set(set3);

        set_trie.del_set_wo_checking(set3);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(all_supersets, vec![vec![1, 2, 3]]);
    }

    #[test]
    fn test_del_set_wo_checking_3() {
        let mut set_trie = SetTrie::new();
        set_trie.insert_new_set(&[1, 4, 5, 7]);
        set_trie.insert_new_set(&[1, 4, 5, 8]);

        set_trie.del_set_wo_checking(&[1, 4, 5, 7]);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(all_supersets, vec![vec![1, 4, 5, 8],]);
    }
    #[test]
    fn test_del_set_wo_checking_4() {
        let mut set_trie = SetTrie::new();
        set_trie.insert_new_set(&[1, 4, 5, 7]);
        set_trie.insert_new_set(&[1, 4, 5, 6, 8]);

        set_trie.del_set_wo_checking(&[1, 4, 5, 7]);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(all_supersets, vec![vec![1, 4, 5, 6, 8],]);
    }

    #[test]
    fn test_del_set_wo_checking_5() {
        let mut set_trie = SetTrie::new();
        set_trie.insert_new_set(&[1, 4, 5, 7]);
        set_trie.insert_new_set(&[1, 4, 5, 6, 8]);

        set_trie.del_set_wo_checking(&[1, 4, 5, 6, 8]);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(all_supersets, vec![vec![1, 4, 5, 7],]);
    }
    #[test]
    fn test_del_set_wo_checking_6() {
        let mut set_trie = SetTrie::new();
        set_trie.insert_new_set(&[1]);

        set_trie.del_set_wo_checking(&[1]);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(all_supersets, Vec::<Vec<i32>>::new());
    }
    #[test]
    fn test_del_set_wo_checking_7() {
        let mut set_trie = SetTrie::new();
        set_trie.insert_new_set(&[1, 2]);

        set_trie.del_set_wo_checking(&[1, 2]);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(all_supersets, Vec::<Vec<i32>>::new());
    }
    #[test]
    fn test_del_set_wo_checking_8() {
        let mut set_trie = SetTrie::new();
        set_trie.insert_new_set(&[1, 2]);
        set_trie.insert_new_set(&[1, 3]);

        set_trie.del_set_wo_checking(&[1, 2]);
        let all_supersets = set_trie.get_all_supersets();
        assert_eq!(all_supersets, vec![vec![1, 3]]);
    }
}
