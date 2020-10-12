use std::any::{Any, TypeId};

pub fn downcast_ref<T: Any, V: Any>(value: &T) -> Option<&V> {
    if value.type_id() == TypeId::of::<V>() {
        unsafe { Some(&*(value as *const T as *const V)) }
    } else {
        None
    }
}
