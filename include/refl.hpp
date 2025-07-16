// The MIT License (MIT)
//
// Copyright (c) 2020 Veselin Karaganev (@veselink1) and Contributors
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#ifndef REFL_INCLUDE_HPP
#define REFL_INCLUDE_HPP

#include <cstdint>
#include <stddef.h> // size_t
#include <tuple>

/**
 * @brief The top-level refl-cpp namespace
 * It contains a few core refl-cpp namespaces and directly exposes core classes and functions.
 * <ul>
 * <li>util - utility functions (for_each, map_to_tuple, etc.)</li>
 * <li>trait - type-traits and other operations on types (is_function_v, map_t, etc.)</li>
 * <li>runtime - utility functions and classes that always have a runtime overhead (proxy<T>, debug_str, etc.)</li>
 * <li>member - contains the empty classes member and function (used for tagging)</li>
 * <li>descriptor - contains the non-specialized member types (type|field_descriptor<T, N>, and operations on them (get_property, get_display_name, etc.))</li>
 * </ul>
 *
 * using util::type_list; <br>
 * using descriptor::type_descriptor; <br>
 * using descriptor::field_descriptor; <br>
 * using descriptor::function_descriptor; <br>
 * using util::const_string; <br>
 * using util::make_const_string; <br>
 */
namespace refl
{
    /**
     * @brief Contains utility types and functions for working with those types.
     */
    namespace util
    {
        /**
         * Represents a compile-time list of types provided as variadic template parameters.
         * type_list is an empty TrivialType. Instances of it can freely be created to communicate
         * the list of represented types. type_lists support many standard operations that are
         * implicitly available with ADL-lookup. type_list is used by refl-cpp mostly to represent
         * the list of refl::field_descriptor, refl::function_descriptor specializations that
         * allow the compile-time reflection of a type's members.
         *
         * @see refl::util::for_each
         * @see refl::util::map_to_array
         * @see refl::util::map_to_tuple
         * @see refl::member_list
         *
         * # Examples
         * ```
         * for_each(type_list<int, float>(), [](auto) { ... });
         * ```
         */
        template <typename... Ts>
        struct type_list
        {
            /** The number of types in this type_list */
            static constexpr intptr_t size = sizeof...(Ts);

            /** Conversion */
            template<template<typename...> class U>
            using to = U<Ts...>;
        };

        template <typename T>
        struct type_list<T>
        {
            typedef T type;
            static constexpr intptr_t size = 1;

            /** Conversion */
            template<template<typename...> class U>
            using to = U<T>;
        };

        template <typename T>
        using type_tag = type_list<T>;

    } // namespace util

    using util::type_list;
    using util::type_tag;

    /**
     * The contents of the refl::detail::macro_exports namespace
     * is implicitly available in the context of REFL_TYPE/FIELD/FUNC macros.
     * It is used to export the refl::attr:: standard attributes.
     */
    namespace detail
    {
        namespace macro_exports
        {
        }
    }

} // namespace refl

/**
 * refl_impl is an internal namespace that should not be used by the users of refl-cpp.
 */
namespace refl_impl
{
    /**
     * Contains the generated metadata types.
     * (i.e. type_info__)
     */
    namespace metadata
    {
        // Import everyting from macro_exports here to make it visible in REFL_ macro context.
        using namespace refl::detail::macro_exports;
    } // namespace metadata

} // namespace refl_impl

namespace refl
{
    namespace descriptor
    {
        template <typename>
        class type_descriptor;
    } // namespace descriptor

    /**
     * @brief Provides type-level operations for refl-cpp related use-cases.
     *
     * The refl::trait namespace provides type-level operations useful
     * for compile-time metaprogramming.
     */
    namespace trait
    {/**
         * Removes all reference and cv-qualifiers from T.
         * Equivalent to std::remove_cvref which is not currently
         * available on all C++17 compilers.
         */
        template <typename T>
        struct remove_qualifiers
        {
            typedef std::remove_cv_t<std::remove_reference_t<T>> type;
        };

        /**
         * Removes all reference and cv-qualifiers from T.
         * Equivalent to std::remove_cvref_t which is not currently
         * available on all C++17 compilers.
         */
        template <typename T>
        using remove_qualifiers_t = typename remove_qualifiers<T>::type;

        namespace detail
        {

            template <size_t D, size_t N, typename... Ts>
            struct get;

            template <size_t D, size_t N>
            struct get<D, N>
            {
                static_assert(N > 0, "Missing arguments list for get<N, Ts...>!");
            };

            template <size_t N, typename T, typename... Ts>
            struct get<1, N, T, Ts...> : public get<
                                             (N > 16 ? (N > 64 ? 64 : 16) : 1),
                                             N - 1, Ts...>
            {
            };

            template <typename T, typename... Ts>
            struct get<1, 0, T, Ts...>
            {
                typedef T type;
            };

            template <typename T, typename... Ts>
            struct get<16, 0, T, Ts...>
            {
                typedef T type;
            };

            template <typename T, typename... Ts>
            struct get<64, 0, T, Ts...>
            {
                typedef T type;
            };

            template <
                size_t N, typename T0, typename T1, typename T2, typename T3,
                typename T4, typename T5, typename T6, typename T7, typename T8,
                typename T9, typename T10, typename T11, typename T12,
                typename T13, typename T14, typename T15, typename... Ts>
            struct get<
                16, N, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12,
                T13, T14, T15, Ts...> : get<1, N - 16, Ts...>
            {
            };

            template <
                size_t N, typename T0, typename T1, typename T2, typename T3,
                typename T4, typename T5, typename T6, typename T7, typename T8,
                typename T9, typename T10, typename T11, typename T12,
                typename T13, typename T14, typename T15, typename T16,
                typename T17, typename T18, typename T19, typename T20,
                typename T21, typename T22, typename T23, typename T24,
                typename T25, typename T26, typename T27, typename T28,
                typename T29, typename T30, typename T31, typename T32,
                typename T33, typename T34, typename T35, typename T36,
                typename T37, typename T38, typename T39, typename T40,
                typename T41, typename T42, typename T43, typename T44,
                typename T45, typename T46, typename T47, typename T48,
                typename T49, typename T50, typename T51, typename T52,
                typename T53, typename T54, typename T55, typename T56,
                typename T57, typename T58, typename T59, typename T60,
                typename T61, typename T62, typename T63, typename... Ts>
            struct get<
                64, N, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12,
                T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25,
                T26, T27, T28, T29, T30, T31, T32, T33, T34, T35, T36, T37, T38,
                T39, T40, T41, T42, T43, T44, T45, T46, T47, T48, T49, T50, T51,
                T52, T53, T54, T55, T56, T57, T58, T59, T60, T61, T62, T63,
                Ts...> : get<1, N - 64, Ts...>
            {
            };
        }

        /// \private
        template <size_t, typename>
        struct get;

        /**
         * Provides a member typedef type which is the
         * N-th type in the provided type_list.
         *
         * \code{.cpp}
         * typename get<0, type_list<int, float>>::type -> int
         * typename get<1, type_list<int, float>>::type -> float
         * \endcode
         */
        template <size_t N, typename... Ts>
        struct get<N, type_list<Ts...>> : detail::get<1, N, Ts...>
        {
        };

        /**
         * The N-th type in the provided type_list.
         * @see get
         */
        template <size_t N, typename TypeList>
        using get_t = typename get<N, TypeList>::type;

        /// \private
        template <typename>
        struct as_type_list;

        /**
         * Provides a member typedef type which is a type_list with
         * template type parameters equivalent to the type parameters of the provided
         * type. The provided type must be a template instance.
         *
         * \code{.cpp}
         * typename as_type_list<std::tuple<int, float>>::type -> type_list<int, float>
         * \endcode
         */
        template <template <typename...> typename T, typename... Ts>
        struct as_type_list<T<Ts...>>
        {
            typedef type_list<Ts...> type;
        };

        /// \private
        template <typename T>
        struct as_type_list : as_type_list<remove_qualifiers_t<T>>
        {
        };

        /**
         * A typedef for a type_list with
         * template type parameters equivalent to the type parameters of the provided
         * type. The provided type must be a template instance.
         * @see as_type_list
         */
        template <typename T>
        using as_type_list_t = typename as_type_list<T>::type;

        /**
         * Concatenates N lists together.
         *
         * \code{.cpp}
         * typename concat<type_list<int, float>, type_list<double>, type_list<long>>::type -> type_list<int, float, double, long>
         * \endcode
         */
        template <typename...>
        struct concat;

        /// \private
        template <>
        struct concat<>
        {
            using type = type_list<>;
        };

        /// \private
        template <typename... Ts>
        struct concat<type_list<Ts...>>
        {
            using type = type_list<Ts...>;
        };

        /**
         * Concatenates two lists together.
         */
        /// \private
        template <typename... Ts, typename... Us>
        struct concat<type_list<Ts...>, type_list<Us...>>
        {
            using type = type_list<Ts..., Us...>;
        };

        /**
         * Concatenates N lists together.
         */
        /// \private
        template <typename TypeList1, typename TypeList2, typename... TypeLists>
        struct concat<TypeList1, TypeList2, TypeLists...> : concat<typename concat<TypeList1, TypeList2>::type, TypeLists...>
        {
        };

        /**
         * Concatenates two lists together.
         * @see concat
         */
        template <typename... Ts>
        using concat_t = typename concat<Ts...>::type;

        /**
         * Appends a type to the list.
         */
        template <typename T, typename TypeList>
        struct append : concat<TypeList, type_list<T>>
        {
        };

        /**
         * Appends a type to the list.
         * @see prepend
         */
        template <typename T, typename TypeList>
        using append_t = typename append<T, TypeList>::type;

        template <typename, typename>
        struct prepend;

        /**
         * Prepends a type to the list.
         */
        template <typename T, typename TypeList>
        struct prepend : concat<type_list<T>, TypeList>
        {
        };

        /**
         * Prepends a type to the list.
         * @see prepend
         */
        template <typename T, typename TypeList>
        using prepend_t = typename prepend<T, TypeList>::type;

        namespace detail
        {
            template <template<typename> typename, typename...>
            struct map_impl;

            template <template<typename> typename Mapper>
            struct map_impl<Mapper>
            {
                using type = type_list<>;
            };

            template <template<typename> typename Mapper, typename Head, typename ...Tail>
            struct map_impl<Mapper, Head, Tail...>
            {
                using type = typename prepend<typename Mapper<Head>::type,
                    typename map_impl<Mapper, Tail...>::type>::type;
            };
        }

        /// \private
        template <template<typename> typename, typename>
        struct map;

        /**
         * Transforms a type_list according to a predicate template.
         *
         * \code{.cpp}
         * typename map<std::add_reference, type_list<int, float&, double>>::type -> type_list<int&, float&, double&>
         * \endcode
         */
        template <template<typename> typename Mapper, typename... Ts>
        struct map<Mapper, type_list<Ts...>>
        {
            using type = typename detail::map_impl<Mapper, Ts...>::type;
        };

        /**
         * Transforms a type_list according to a predicate template
         * with a typedef named "type" (e.g. std::remove_reference)
         * @see map
         */
        template <template<typename> typename Mapper, typename... Ts>
        using map_t = typename map<Mapper, Ts...>::type;

        namespace detail
        {
            template <typename T>
            struct is_instance : public std::false_type {};

            template <template<typename...> typename T, typename... Args>
            struct is_instance<T<Args...>> : public std::true_type {};
        } // namespace detail

        /**
         * Detects whether T is a template specialization.
         * Inherits from std::bool_constant<>.
         *
         * \code{.cpp}
         * is_instance<type_list<>>::value -> true
         * is_instance<int>::value -> false
         * \endcode
         */
        template <typename T>
        struct is_instance : detail::is_instance<T>
        {
        };

        /**
         * Detects whether T is a template specialization.
         * @see is_instance
         */
        template <typename T>
        [[maybe_unused]] static constexpr bool is_instance_v{ is_instance<T>::value };

        namespace detail
        {
            /**
             * Checks if T == U<Args...>.
             * If U<Args...> != T or is invalid the result is false.
             */
            template <typename T, template<typename...> typename U, typename... Args>
            struct is_same_template
            {
                template <template<typename...> typename V, typename = V<Args...>>
                static auto test(int) -> std::is_same<V<Args...>, T>;

                template <template<typename...> typename V>
                static std::false_type test(...);

                static constexpr bool value{decltype(test<U>(0))::value};
            };

            template <template<typename...> typename T, typename U>
            struct is_instance_of : public std::false_type {};

            template <template<typename...> typename T, template<typename...> typename U, typename... Args>
            struct is_instance_of<T, U<Args...>> : public is_same_template<U<Args...>, T, Args...>
            {
            };
        }

        /**
         * Detects whther the type U is a template specialization of T.
         * (e.g. is_instance_of<std::vector<>, std::vector<int>>)
         * Inherits from std::bool_constant<>.
         *
         * \code{.cpp}
         * is_instance_of<type_list, type_list<int>>::value -> true
         * is_instance_of<type_list, std::tuple<int>>::value -> false
         * \endcode
         */
        template <template<typename...>typename T, typename U>
        struct is_instance_of : detail::is_instance_of<T, std::remove_cv_t<U>>
        {
        };

        /**
         * Detects whther the type U is a template specialization of T.
         * @see is_instance_of_v
         */
        template <template<typename...>typename T, typename U>
        [[maybe_unused]] static constexpr bool is_instance_of_v{ is_instance_of<T, U>::value };

        /// \private
        template <typename, typename>
        struct contains;

        /**
         * Checks whether T is contained in the list of types.
         * Inherits from std::bool_constant<>.
         *
         * \code{.cpp}
         * contains<int, type_list<int, float>>::value -> true
         * contains<double, type_list<int, float>>::value -> false
         * \endcode
         */
        template <typename T, typename... Ts>
        struct contains<T, type_list<Ts...>> : std::disjunction<std::is_same<std::remove_cv_t<T>, std::remove_cv_t<Ts>>...>
        {
        };

        /**
         * Checks whether T is contained in the list of types.
         * @see contains
         */
        template <typename T, typename TypeList>
        [[maybe_unused]] static constexpr bool contains_v = contains<T, TypeList>::value;

        /// \private
        template <template<typename...> typename, typename>
        struct contains_instance;

        /**
         * Checks whether an instance of the template T is contained in the list of types.
         * Inherits from std::bool_constant<>.
         *
         * \code{.cpp}
         * contains_instance<std::tuple, type_list<int, float, std::tuple<short, double>>>::value -> true
         * contains_instance<std::vector, type_list<int, float, std::tuple<short, double>>>::value -> false
         * \endcode
         */
        template <template<typename...> typename T, typename... Ts>
        struct contains_instance<T, type_list<Ts...>> : std::disjunction<trait::is_instance_of<T, std::remove_cv_t<Ts>>...>
        {
        };

        /**
         * Checks whether an instance of the template T is contained in the list of types.
         * @see contains_instance
         */
        template <template<typename...> typename T, typename TypeList>
        [[maybe_unused]] static constexpr bool contains_instance_v = contains_instance<T, TypeList>::value;

        namespace detail
        {
            template <template<typename...> typename T, ptrdiff_t N, typename... Ts>
            constexpr ptrdiff_t index_of_instance() noexcept
            {
                if constexpr (sizeof...(Ts) <= N) return -1;
                else if constexpr (is_instance_of_v<T, trait::get_t<N, type_list<Ts...>>>) return N;
                else return index_of_instance<T, N + 1, Ts...>();
            }

            // This variable template was introduced to fix the build on VS2017, which
            // chokes when invoking index_of_instance() directly from struct index_of_instance.
            template <template<typename...> typename T, ptrdiff_t N, typename... Ts>
            static constexpr ptrdiff_t index_of_instance_v = index_of_instance<T, N, Ts...>();
        } // namespace detail

        /// \private
        template <template<typename...> typename, typename>
        struct index_of_instance;

        /**
         * The index of the type in the type list that is a template instance of T, -1 if it doesn't exist.
         * @see contains_instance
         */
        template <template<typename...> typename T, typename... Ts>
        struct index_of_instance<T, type_list<Ts...>> : std::integral_constant<ptrdiff_t, detail::index_of_instance_v<T, 0, Ts...>>
        {
        };

        /**
         * The index of the type in the type list that is a template instance of T, -1 if it doesn't exist.
         * @see index_of_instance
         */
        template <template<typename...> typename T, typename TypeList>
        static constexpr ptrdiff_t index_of_instance_v = index_of_instance<T, TypeList>::value;

        namespace detail
        {
            template <typename, typename>
            struct unique_impl;

            template <typename UniqueList>
            struct unique_impl<UniqueList, type_list<>>
            {
                using type = UniqueList;
            };

            template <typename UniqueList, typename T, typename... Ts>
            struct unique_impl<UniqueList, type_list<T, Ts...>> :
                std::conditional_t<contains_v<T, UniqueList>,
                    unique_impl<UniqueList, type_list<Ts...>>,
                    unique_impl<append_t<T, UniqueList>, type_list<Ts...>>>
            {
            };
        } // namespace detail

        /**
         * Creates a new list containing the repeating elements in the source list only once.
         *
         * \code{.cpp}
         * typename unique<type_list<int, float, int>>::type -> type_list<int, float>
         * \endcode
         */
        template <typename T>
        struct unique : detail::unique_impl<type_list<>, T>
        {
        };

        /**
         * Creates a new list containing the repeating elements in the source list only once.
         */
        template <typename T>
        using unique_t = typename unique<T>::type;

    } // namespace trait

    namespace util
    {
        /**
         * Ignores all parameters. Can take an optional template parameter
         * specifying the return type of ignore. The return object is iniailized by {}.
         */
        template <typename T = int, typename... Ts>
        constexpr int ignore(Ts&&...) noexcept
        {
            return {};
        }

        /** Returns the value of type U, where U is a template instance of T. */
        template <template<typename...> typename T, typename... Ts>
        constexpr auto& get_instance(std::tuple<Ts...>& ts) noexcept
        {
            static_assert((... || trait::is_instance_of_v<T, Ts>), "The tuple does not contain a type that is a template instance of T!");
            constexpr size_t idx = static_cast<size_t>(trait::index_of_instance_v<T, type_list<Ts...>>);
            return std::get<idx>(ts);
        }

        /** Returns the value of type U, where U is a template instance of T. */
        template <template<typename...> typename T, typename... Ts>
        constexpr const auto& get_instance(const std::tuple<Ts...>& ts) noexcept
        {
            static_assert((... || trait::is_instance_of_v<T, Ts>), "The tuple does not contain a type that is a template instance of T!");
            constexpr size_t idx = static_cast<size_t>(trait::index_of_instance_v<T, type_list<Ts...>>);
            return std::get<idx>(ts);
        }
    } // namespace util

    /**
     * @brief Contains the definitions of the built-in attributes
     *
     * Contains the definitions of the built-in attributes which
     * are implicitly available in macro context as well as the
     * attr::usage namespace which contains constraints
     * for user-provieded attributes.
     *
     * # Examples
     * ```
     * REFL_TYPE(Point, debug(custom_printer))
     *     REFL_FIELD(x)
     *     REFL_FIELD(y)
     * REFL_END
     * ```
     */
    namespace attr
    {
        /**
         * @brief Contains a number of constraints applicable to refl-cpp attributes.
         *
         * Contains base types which create compile-time constraints
         * that are verified by refl-cpp. These base-types must be inherited
         * by custom attribute types.
         */
        namespace usage
        {
            /**
             * Specifies that an attribute type inheriting from this type can
             * only be used with REFL_TYPE()
             */
            struct type {};
        }

        /**
         * Used to specify the base types of the target type.
         */
        template <typename... Ts>
        struct base_types : usage::type
        {
            /** An alias for a type_list of the base types. */
            typedef type_list<Ts...> list_type;

            /** An instance of a type_list of the base types. */
            static constexpr list_type list{ };
        };

        /**
         * Used to specify the base types of the target type.
         */
        template <typename... Ts>
        [[maybe_unused]] static constexpr base_types<Ts...> bases{ };
    } // namespace attr

    namespace detail
    {
        namespace macro_exports
        {
            using attr::bases;
        }
    }

    namespace trait
    {
        /**
         * Detects whether the type T is a type_descriptor.
         * Inherits from std::bool_constant<>.
         */
        template <typename T>
        struct is_type : is_instance_of<descriptor::type_descriptor, T>
        {
        };

        /**
         * Detects whether the type T is a type_descriptor.
         * @see is_type
         */
        template <typename T>
        [[maybe_unused]] constexpr bool is_type_v{ is_type<T>::value };
    } // namespace trait

    /**
     * @brief Contains the basic reflection primitives
     * as well as functions operating on those primitives
     */
    namespace descriptor
    {
        namespace detail
        {
            template <typename T>
            using attribute_types = trait::as_type_list_t<std::remove_cv_t<decltype(refl::detail::type_info<T>::attributes)>>;

            template <typename>
            struct flatten;

            template <typename... TypeLists>
            struct flatten<type_list<TypeLists...>> : trait::concat<TypeLists...>
            {
            };

            template <typename T, typename Base>
            static constexpr void validate_base()
            {
                static_assert(std::is_base_of_v<Base, T>, "Base is not a base type of T!");
            }

            template <typename T, typename... Bases>
            static constexpr void validate_bases(type_list<Bases...>)
            {
                util::ignore((validate_base<T, Bases>(), 0)...);
            }

            template <typename T>
            static constexpr auto get_declared_base_type_list()
            {
                if constexpr (trait::contains_instance_v<attr::base_types, attribute_types<T>>) {
                    using base_types_type = trait::remove_qualifiers_t<decltype(util::get_instance<attr::base_types>(refl::detail::type_info<T>::attributes))>;
                    validate_bases<T>(base_types_type::list);
                    return typename base_types_type::list_type{};
                }
                else {
                    return type_list<>{};
                }
            }

            template <typename T>
            struct declared_base_type_list
            {
                using type = decltype(get_declared_base_type_list<T>());
            };

            template <typename T>
            struct base_type_list;

            template <typename T>
            static constexpr auto get_base_type_list()
            {
                if constexpr (trait::contains_instance_v<attr::base_types, attribute_types<T>>) {
                    using declared_bases = typename declared_base_type_list<T>::type;
                    using rec_bases = typename flatten<trait::map_t<base_type_list, declared_bases>>::type;
                    return trait::unique_t<trait::concat_t<declared_bases, rec_bases>>{};
                }
                else {
                    return type_list<>{};
                }
            }

            template <typename T>
            struct base_type_list
            {
                using type = decltype(get_base_type_list<T>());
            };
        } // namespace detail

        /** Represents a reflected type. */
        template <typename T>
        class type_descriptor
        {
        public:
            /**
             * The declared base types (via base_types<Ts...> attribute) of T.
             * \copydetails refl::descriptor::get_declared_base_types
             */
            typedef typename detail::declared_base_type_list<T>::type declared_base_types;

            /**
             * The declared and inherited base types of T.
             * \copydetails refl::descriptor::get_base_types
             */
            typedef typename detail::base_type_list<T>::type base_types;

            /**
             * The declared base types (via base_types<Ts...> attribute) of T.
             * \copydetails refl::descriptor::get_declared_base_types
             */
            static constexpr declared_base_types declared_bases{};

            /**
             * The declared  and inherited base types of T.
             * \copydetails refl::descriptor::get_base_types
             */
            static constexpr base_types bases{};
        };

        /**
         * Returns a type_list of the declared base types of the type.
         * Combine with reflect_types to obtain type_descriptors for those types.
         * @see reflect_types
         *
         * \code{.cpp}
         * struct Animal {};
         * REFL_AUTO(type(Animal))
         * struct Mammal : Animal {};
         * REFL_AUTO(type(Mammal, bases<Animal>))
         * struct Dog : Mammal {}:
         * REFL_AUTO(type(Dog, bases<Mammal>))
         *
         * get_base_types(reflect<Dog>()) -> type_list<Mammal>
         * \endcode
         */
        template <typename TypeDescriptor>
        constexpr auto get_declared_base_types(TypeDescriptor t) noexcept
        {
            static_assert(trait::is_type_v<TypeDescriptor>);
            return t.declared_bases;
        }

        /**
         * Returns a type_list of the declared and inherited base types of the type.
         * Combine with reflect_types to obtain type_descriptors for those types.
         * @see reflect_types
         *
         * \code{.cpp}
         * struct Animal {};
         * REFL_AUTO(type(Animal))
         * struct Mammal : Animal {};
         * REFL_AUTO(type(Mammal, bases<Animal>))
         * struct Dog : Mammal {}:
         * REFL_AUTO(type(Dog, bases<Mammal>))
         *
         * get_base_types(reflect<Dog>()) -> type_list<Mammal, Animal>
         * \endcode
         */
        template <typename TypeDescriptor>
        constexpr auto get_base_types(TypeDescriptor t) noexcept
        {
            static_assert(trait::is_type_v<TypeDescriptor>);
            return t.bases;
        }

        namespace detail
        {
            template <typename T>
            struct get_type_descriptor
            {
                typedef type_descriptor<T> type;
            };
        } // namespace detail

        /**
         * Checks if a type has a bases attribute.
         *
         * @deprecated Use has_base_types in combination with reflect_types instead.
         * @see refl::attr::bases
         * @see refl::descriptor::get_bases
         *
         * \code{.cpp}
         * REFL_AUTO(type(Dog, bases<Animal>))
         * has_bases(reflect<Dog>()) -> true
         * \endcode
         */
        template <typename TypeDescriptor>
        [[deprecated]] constexpr auto has_bases(TypeDescriptor t) noexcept
        {
            static_assert(trait::is_type_v<TypeDescriptor>);
            return has_attribute<attr::base_types>(t);
        }

        /**
         * Returns a list of the type_descriptor<T>s of the base types of the target,
         * as specified by the bases<A, B, ...> attribute.
         *
         * @deprecated Use get_base_types in combination with reflect_types instead.
         * @see refl::attr::bases
         * @see refl::descriptor::has_bases
         *
         * \code{.cpp}
         * REFL_AUTO(type(Dog, bases<Animal>))
         * get_bases(reflect<Dog>()) -> type_list<type_descriptor<Animal>>
         * \endcode
         */
        template <typename TypeDescriptor>
        [[deprecated]] constexpr auto get_bases(TypeDescriptor t) noexcept
        {
            static_assert(trait::is_type_v<TypeDescriptor>);
            static_assert(has_bases(t), "Target type does not have a bases<A, B, ...> attribute.");

            constexpr auto bases = get_attribute<attr::base_types>(t);
            using base_types = typename decltype(bases)::list_type;
            return trait::map_t<detail::get_type_descriptor, base_types>{};
        }
    } // namespace descriptor

    using descriptor::type_descriptor;

    /** Returns the type descriptor for the type T. */
    template<typename T>
    constexpr type_descriptor<T> reflect() noexcept
    {
        return {};
    }

    /** Returns the type descriptor for the non-qualified type T. */
    template<typename T>
    constexpr type_descriptor<T> reflect(const T&) noexcept
    {
        return {};
    }
} // namespace refl

namespace refl::detail
{
    constexpr bool validate_attr_unique(type_list<>) noexcept
    {
        return true;
    }

    /** Statically asserts that all types in Ts... are unique. */
    template <typename T, typename... Ts>
    constexpr bool validate_attr_unique(type_list<T, Ts...>) noexcept
    {
        constexpr bool cond = (... && (!std::is_same_v<T, Ts> && validate_attr_unique(type_list<Ts>{})));
        static_assert(cond, "Some of the attributes provided have duplicate types!");
        return cond;
    }

    template <typename Req, typename Attr>
    constexpr bool validate_attr_usage() noexcept
    {
        return std::is_base_of_v<Req, Attr>;
    }

    /**
     * Statically asserts that all arguments inherit
     * from the appropriate bases to be used with Req.
     * Req must be one of the types defined in attr::usage.
     */
    template <typename Req, typename... Args>
    constexpr auto make_attributes(Args&&... args) noexcept
    {
        constexpr bool check_unique = validate_attr_unique(type_list<Args...>{});
        static_assert(check_unique, "Some of the supplied attributes cannot be used on this declaration!");

        constexpr bool check_usage = (... && validate_attr_usage<Req, trait::remove_qualifiers_t<Args>>());
        static_assert(check_usage, "Some of the supplied attributes cannot be used on this declaration!");

        return std::make_tuple(std::forward<Args>(args)...);
    }

} // namespace refl::detail

#endif // REFL_INCLUDE_HPP
