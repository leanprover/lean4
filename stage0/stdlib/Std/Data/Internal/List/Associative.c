// Lean compiler output
// Module: Std.Data.Internal.List.Associative
// Imports: Init.Data.BEq Init.Data.Nat.Simproc Init.Data.Option.Attach Init.Data.List.Perm Init.Data.List.Find Init.Data.List.MinMax Init.Data.List.Monadic Std.Data.Internal.List.Defs Std.Classes.Ord.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f___at_Std_Internal_List_minEntry_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKeyD___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x3f___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x21___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_min_x3f___at_Std_Internal_List_minEntry_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey___spec__4___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x21___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_List_getValueCast_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Internal_List_insertListConst___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_panic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x21___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKeyD___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Internal_List_insertListConst___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x3f___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___at_Std_Internal_List_maxKey___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKeyD___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKeyD___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x21___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Internal_List_minEntry_x3f___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___at_Std_Internal_List_maxKey___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Internal_List_getValueCast_x21___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKeyD___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Internal_List_minEntry_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_List_getValueCast_x21___rarg___closed__2;
lean_object* l_List_min_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKeyD___spec__4___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x21___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
uint8_t l_Ordering_isLE(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit(lean_object*);
static lean_object* l_Std_Internal_List_getValueCast_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x21___spec__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_8);
x_10 = lean_apply_2(x_1, x_8, x_2);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_14);
x_16 = lean_apply_2(x_1, x_14, x_2);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getEntry_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_3(x_3, x_6, x_7, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getEntry_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_3(x_3, x_6, x_7, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_keys_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_7, x_2);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getValue_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_3(x_3, x_6, x_7, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_getValue_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_8, x_3);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_9);
x_2 = lean_box(0);
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getValueCast_x3f___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_apply_2(x_2, x_5, lean_box(0));
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_2, x_7, lean_box(0));
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_4, x_6, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Option_dmap_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_List_containsKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_7, x_2);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_containsKey___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_containsKey___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Internal_List_containsKey___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_Internal_List_getEntry_x3f___rarg(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getEntry___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_Internal_List_getValue_x3f___rarg(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getValue___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_Internal_List_getValueCast_x3f___rarg(x_1, lean_box(0), x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getValueCast___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_List_getValueCast_x3f___rarg(x_1, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getValueCastD___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCastD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_List_getValueCastD___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_List_getValueCast_x21___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_Internal_List_getValueCast_x21___rarg___closed__1;
x_2 = l_Std_Internal_List_getValueCast_x21___rarg___closed__2;
x_3 = lean_unsigned_to_nat(21u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_Internal_List_getValueCast_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Internal_List_getValueCast_x3f___rarg(x_1, lean_box(0), x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_Internal_List_getValueCast_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueCast_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getValueCast_x21___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_List_getValue_x3f___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getValueD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValueD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_List_getValueD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_List_getValue_x3f___rarg(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_Internal_List_getValueCast_x21___rarg___closed__4;
x_7 = l_panic___rarg(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getValue_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getValue_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_7);
x_8 = lean_apply_2(x_1, x_7, x_2);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getKey_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_Internal_List_getKey_x3f___rarg(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getKey___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_List_getKey_x3f___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getKeyD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKeyD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_List_getKeyD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_List_getKey_x3f___rarg(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_Internal_List_getValueCast_x21___rarg___closed__4;
x_7 = l_panic___rarg(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_getKey_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_getKey_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_10);
x_12 = lean_apply_2(x_1, x_10, x_2);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Std_Internal_List_replaceEntry___rarg(x_1, x_2, x_3, x_9);
lean_ctor_set(x_4, 1, x_14);
return x_4;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_16);
x_18 = lean_apply_2(x_1, x_16, x_2);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
x_21 = l_Std_Internal_List_replaceEntry___rarg(x_1, x_2, x_3, x_15);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
else
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_25);
x_28 = lean_apply_2(x_1, x_25, x_2);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
x_31 = l_Std_Internal_List_replaceEntry___rarg(x_1, x_2, x_3, x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
if (lean_is_scalar(x_27)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_27;
}
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_replaceEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_replaceEntry___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_9);
x_11 = lean_apply_2(x_1, x_9, x_2);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Std_Internal_List_eraseKey___rarg(x_1, x_2, x_8);
lean_ctor_set(x_3, 1, x_13);
return x_3;
}
else
{
lean_free_object(x_6);
lean_dec(x_10);
lean_dec(x_9);
lean_free_object(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_15);
x_17 = lean_apply_2(x_1, x_15, x_2);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
x_20 = l_Std_Internal_List_eraseKey___rarg(x_1, x_2, x_14);
lean_ctor_set(x_3, 1, x_20);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_23);
x_26 = lean_apply_2(x_1, x_23, x_2);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
if (lean_is_scalar(x_25)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_25;
}
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = l_Std_Internal_List_eraseKey___rarg(x_1, x_2, x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_eraseKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_eraseKey___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_Internal_List_containsKey___rarg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Std_Internal_List_replaceEntry___rarg(x_1, x_2, x_3, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_insertEntry___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Std_Internal_List_containsKey___rarg(x_1, x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertEntryIfNew(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_insertEntryIfNew___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__List_filterMap_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__List_forIn_x27__cons_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_Std_Internal_List_insertEntry___rarg(x_1, x_6, x_7, x_2);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_insertList___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Prod_toSigma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_Prod_toSigma___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Internal_List_insertListConst___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Std_Internal_List_Prod_toSigma___rarg(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Std_Internal_List_Prod_toSigma___rarg(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Internal_List_insertListConst___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_mapTR_loop___at_Std_Internal_List_insertListConst___spec__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_Std_Internal_List_insertListConst___spec__1___rarg(x_3, x_4);
x_6 = l_Std_Internal_List_insertList___rarg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_insertListConst___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
lean_inc(x_1);
x_7 = l_Std_Internal_List_insertEntryIfNew___rarg(x_1, x_4, x_6, x_2);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_insertListIfNewUnit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Internal_List_insertListIfNewUnit___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Std_Internal_List_getValueCast_x3f___rarg(x_1, lean_box(0), x_3, x_5);
x_7 = lean_apply_1(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Std_Internal_List_eraseKey___rarg(x_1, x_3, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_Internal_List_insertEntry___rarg(x_1, x_3, x_9, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_alterKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_alterKey___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___rarg___boxed), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_alterKey_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_Internal_List_getValue_x3f___rarg(x_1, x_2, x_4);
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_Internal_List_eraseKey___rarg(x_1, x_2, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_Internal_List_insertEntry___rarg(x_1, x_2, x_8, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_alterKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_Const_alterKey___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_Const_alterKey_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Std_Internal_List_getValueCast_x3f___rarg(x_1, lean_box(0), x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_1(x_4, x_7);
x_9 = l_Std_Internal_List_replaceEntry___rarg(x_1, x_3, x_8, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_modifyKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_modifyKey___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Std_Internal_List_getValue_x3f___rarg(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_3, x_6);
x_8 = l_Std_Internal_List_replaceEntry___rarg(x_1, x_2, x_7, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_Const_modifyKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_Const_modifyKey___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Option_isSome_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Option_getD_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_leSigmaOfOrd(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_2(x_1, x_4, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Ordering_isLE(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_instDecidableLESigma__std___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_4, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Ordering_isLE(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Internal_List_minEntry_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Ordering_isLE(x_9);
if (x_10 == 0)
{
lean_dec(x_2);
x_2 = x_4;
x_3 = x_5;
goto _start;
}
else
{
lean_dec(x_4);
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Internal_List_minEntry_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___at_Std_Internal_List_minEntry_x3f___spec__2___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___at_Std_Internal_List_minEntry_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_foldl___at_Std_Internal_List_minEntry_x3f___spec__2___rarg(x_1, x_4, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_min_x3f___at_Std_Internal_List_minEntry_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_min_x3f___at_Std_Internal_List_minEntry_x3f___spec__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_min_x3f___at_Std_Internal_List_minEntry_x3f___spec__1___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minEntry_x3f___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_min_x3f___at_Std_Internal_List_minEntry_x3f___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKey_x3f___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minEntry_x3f__cons_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_Internal_List_Associative_0__List_getLast_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_Internal_List_minKey_x3f___rarg(x_1, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKey___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_minKey_x3f___rarg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_Internal_List_getValueCast_x21___rarg___closed__4;
x_6 = l_panic___rarg(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKey_x21___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_minKey_x3f___rarg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKeyD___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_minKeyD___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_5, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Ordering_isLE(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x3f___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x3f___spec__3___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x3f___spec__3___rarg), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_List_min_x3f___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x3f___spec__2___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x3f___spec__2___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x3f___spec__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x3f___spec__1___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_maxKey_x3f___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_5, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Ordering_isLE(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey___spec__4___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey___spec__4___rarg), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_List_min_x3f___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey___spec__3___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey___spec__3___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey___spec__2___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___at_Std_Internal_List_maxKey___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey___spec__2___rarg(x_1, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey___at_Std_Internal_List_maxKey___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKey___at_Std_Internal_List_maxKey___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_minKey___at_Std_Internal_List_maxKey___spec__1___rarg(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_maxKey___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x21___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_5, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Ordering_isLE(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x21___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x21___spec__3___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x21___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKey_x21___spec__3___rarg), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_List_min_x3f___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x21___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x21___spec__2___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKey_x21___spec__2___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x21___spec__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKey_x21___spec__1___rarg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_Internal_List_getValueCast_x21___rarg___closed__4;
x_6 = l_panic___rarg(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKey_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_maxKey_x21___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKeyD___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_5, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Ordering_isLE(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKeyD___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKeyD___spec__4___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKeyD___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Data_Internal_List_Associative_0__Std_Internal_List_minSigmaOfOrd___at_Std_Internal_List_maxKeyD___spec__4___rarg), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_List_min_x3f___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKeyD___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKeyD___spec__3___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKeyD___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_List_minEntry_x3f___at_Std_Internal_List_maxKeyD___spec__3___rarg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKeyD___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKeyD___spec__2___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_minKey_x3f___at_Std_Internal_List_maxKeyD___spec__2___rarg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_List_maxKeyD___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_minKeyD___at_Std_Internal_List_maxKeyD___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_List_maxKeyD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_List_maxKeyD___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_BEq(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Perm(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Internal_List_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Ord_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Internal_List_Associative(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Perm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_List_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Ord_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_List_getValueCast_x21___rarg___closed__1 = _init_l_Std_Internal_List_getValueCast_x21___rarg___closed__1();
lean_mark_persistent(l_Std_Internal_List_getValueCast_x21___rarg___closed__1);
l_Std_Internal_List_getValueCast_x21___rarg___closed__2 = _init_l_Std_Internal_List_getValueCast_x21___rarg___closed__2();
lean_mark_persistent(l_Std_Internal_List_getValueCast_x21___rarg___closed__2);
l_Std_Internal_List_getValueCast_x21___rarg___closed__3 = _init_l_Std_Internal_List_getValueCast_x21___rarg___closed__3();
lean_mark_persistent(l_Std_Internal_List_getValueCast_x21___rarg___closed__3);
l_Std_Internal_List_getValueCast_x21___rarg___closed__4 = _init_l_Std_Internal_List_getValueCast_x21___rarg___closed__4();
lean_mark_persistent(l_Std_Internal_List_getValueCast_x21___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
