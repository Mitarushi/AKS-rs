#[macro_export]
macro_rules! overload {
    ($( $lifetime:lifetime),+ , $trait:ident, $type:ty, $method_name:ident, $method: ident) => {
        overload!( $( $lifetime),+ , $trait, $type, $type, $type, $method_name, $method);
    };
    ($( $lifetime:lifetime),+ , $trait:ident, $type1:ty, $type2: ty, $method_name:ident, $method: ident) => {
        overload!( $( $lifetime),+ , $trait, $type1, $type2, $type1, $method_name, $method);
    };
    ($( $lifetime:lifetime),+ , $trait:ident, $type1:ty, $type2: ty, $output_type: ty, $method_name:ident, $method: ident) => {
        impl <$( $lifetime),+> $trait<$type2> for $type1 {
            type Output = $output_type;

            fn $method_name(self, other: $type2) -> $output_type {
                self.$method(&other)
            }
        }

        impl<$( $lifetime),+> $trait<&$type2> for $type1 {
            type Output = $output_type;

            fn $method_name(self, other: &$type2) -> $output_type {
                self.$method(other)
            }
        }

        impl<$( $lifetime),+> $trait<$type2> for &$type1 {
            type Output = $output_type;

            fn $method_name(self, other: $type2) -> $output_type {
                self.$method(&other)
            }
        }

        impl<$( $lifetime),+> $trait<&$type2> for &$type1 {
            type Output = $output_type;

            fn $method_name(self, other: &$type2) -> $output_type {
                self.$method(other)
            }
        }
    };
}

#[macro_export]
macro_rules! overload_unary {
    ($( $lifetime:lifetime),+ , $trait:ident, $type:ty, $method_name:ident, $method: ident) => {
        impl<$( $lifetime),+> $trait for $type {
            type Output = $type;

            fn $method_name(self) -> $type {
                self.$method()
            }
        }

        impl<$( $lifetime),+> $trait for &$type {
            type Output = $type;

            fn $method_name(self) -> $type {
                self.$method()
            }
        }
    }
}

#[macro_export]
macro_rules! overload_eq {
    ($( $lifetime:lifetime),+ , $trait:ident, $type:ty, $method_name:ident, $method: ident) => {
        impl<$( $lifetime),+> $trait for $type {
            fn $method_name(&self, other: &$type) -> bool {
                self.$method(other)
            }
        }
    }
}
