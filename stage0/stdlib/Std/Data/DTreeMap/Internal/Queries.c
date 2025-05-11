// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Queries
// Imports: Init.Data.Nat.Compare Std.Data.DTreeMap.Internal.Def Std.Data.DTreeMap.Internal.Balanced Std.Data.DTreeMap.Internal.Ordered Std.Classes.Ord.Basic
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___rarg(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___rarg(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___rarg(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___rarg(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__1;
lean_object* l_panic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_foldr___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__1;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___rarg___boxed(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__1;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object*, lean_object*);
extern lean_object* l_Id_instMonad;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___rarg___boxed(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_foldr___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__instCoeTypeForall__std(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___rarg(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__instCoeTypeForall__std(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_4);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
switch (x_8) {
case 0:
{
lean_dec(x_6);
x_3 = x_5;
goto _start;
}
case 1:
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 1;
return x_10;
}
default: 
{
lean_dec(x_5);
x_3 = x_6;
goto _start;
}
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_contains___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instDecidableMem___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_instDecidableMem___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__2_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_inc(x_4);
return x_4;
}
default: 
{
lean_inc(x_3);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_DTreeMap_Internal_Impl_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_4);
x_9 = lean_apply_2(x_1, x_4, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_6);
x_2 = lean_box(0);
x_3 = x_7;
goto _start;
}
case 1:
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = lean_box(0);
x_3 = x_8;
goto _start;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_get_x3f___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_4);
x_10 = lean_apply_2(x_1, x_4, x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_dec(x_9);
lean_dec(x_7);
x_2 = lean_box(0);
x_3 = x_8;
x_5 = lean_box(0);
goto _start;
}
case 1:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
default: 
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_3 = x_9;
x_5 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_get___rarg), 5, 0);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DTreeMap.Internal.Queries", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.get!", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Key is not present in map", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__2;
x_3 = lean_unsigned_to_nat(92u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_4);
x_10 = lean_apply_2(x_1, x_4, x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_dec(x_9);
lean_dec(x_7);
x_2 = lean_box(0);
x_3 = x_8;
goto _start;
}
case 1:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
default: 
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_3 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_1);
x_14 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__4;
x_15 = l_panic___rarg(x_5, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_get_x21___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_4);
x_10 = lean_apply_2(x_1, x_4, x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_dec(x_9);
lean_dec(x_7);
x_2 = lean_box(0);
x_3 = x_8;
goto _start;
}
case 1:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
default: 
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_3 = x_9;
goto _start;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getD___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_getD___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_apply_2(x_1, x_3, x_4);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
switch (x_8) {
case 0:
{
lean_dec(x_6);
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
default: 
{
lean_dec(x_5);
lean_dec(x_4);
x_2 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKey_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_3);
x_8 = lean_apply_2(x_1, x_3, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_6;
x_4 = lean_box(0);
goto _start;
}
case 1:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_7;
x_4 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKey___rarg), 4, 0);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.getKey!", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(131u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_3);
x_8 = lean_apply_2(x_1, x_3, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
case 1:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__2;
x_13 = l_panic___rarg(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_3);
x_8 = lean_apply_2(x_1, x_3, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
case 1:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_8 = lean_apply_2(x_1, x_3, x_4);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
case 1:
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_get_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_6);
x_2 = x_7;
x_4 = lean_box(0);
goto _start;
}
case 1:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_8;
x_4 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_get___rarg), 4, 0);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.Const.get!", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(172u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
case 1:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__2;
x_14 = l_panic___rarg(x_4, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
case 1:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_foldlM___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_3(x_1, x_7, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Std_DTreeMap_Internal_Impl_foldlM___rarg(x_1, x_2, x_3, x_7);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___rarg___lambda__2), 7, 6);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_1);
lean_closure_set(x_11, 4, x_8);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Id_instMonad;
x_5 = l_Std_DTreeMap_Internal_Impl_foldlM___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_foldrM___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_3(x_1, x_2, x_3, x_7);
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Std_DTreeMap_Internal_Impl_foldrM___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___rarg___lambda__2), 7, 6);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_1);
lean_closure_set(x_11, 4, x_7);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_foldr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 4);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_foldr___spec__1___rarg(x_1, x_2, x_7);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_4, x_5, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_foldr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_foldr___spec__1___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_foldr___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldr___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg(x_1, x_2, x_3, x_7);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_1);
lean_closure_set(x_11, 4, x_8);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_forM___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Std_DTreeMap_Internal_Impl_forInStep___rarg(x_1, x_2, x_14, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
lean_inc(x_2);
x_18 = lean_apply_3(x_2, x_3, x_4, x_17);
x_19 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___rarg___lambda__1), 4, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_5);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Std_DTreeMap_Internal_Impl_forInStep___rarg(x_1, x_2, x_3, x_7);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___rarg___lambda__2), 7, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_6);
lean_closure_set(x_11, 4, x_8);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___rarg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1___rarg(x_1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_keys___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_keys___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_keys___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__1___rarg(x_1, x_4);
x_7 = lean_array_push(x_6, x_3);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__2___rarg(x_1, x_4);
x_7 = lean_array_push(x_6, x_3);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__2___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__1___rarg(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_keysArray___spec__2___rarg(x_5, x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_keysArray___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1___rarg(x_1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_values___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_values___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_values___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__1___rarg(x_1, x_4);
x_7 = lean_array_push(x_6, x_3);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__2___rarg(x_1, x_4);
x_7 = lean_array_push(x_6, x_3);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__2___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__1___rarg(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_valuesArray___spec__2___rarg(x_5, x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_valuesArray___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1___rarg(x_1, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_toList___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_toList___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_toList___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1___rarg(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2___rarg(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1___rarg(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2___rarg(x_5, x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_toArray___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_toArray___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_toArray___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1___rarg(x_1, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_toList___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at_Std_DTreeMap_Internal_Impl_Const_toList___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_Const_toList___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1___rarg(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2___rarg(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1___rarg(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1;
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2___rarg(x_5, x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at_Std_DTreeMap_Internal_Impl_Const_toArray___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_Const_toArray___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_2) == 0)
{
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntry_x3f___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_9(x_4, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_3, x_16, x_17, x_18, x_19);
return x_20;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
x_2 = lean_box(0);
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntry___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_minEntry___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_10(x_4, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_9, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_5(x_3, x_16, x_17, x_18, x_19, lean_box(0));
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.minEntry!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Map is empty", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(295u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
x_2 = x_3;
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__3;
x_9 = l_panic___rarg(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minEntryD___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_minEntryD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_10, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_2) == 0)
{
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_9(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_3, x_16, x_17, x_18, x_19);
return x_20;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
x_2 = lean_box(0);
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_maxEntry___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_maxEntry___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_10(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_5(x_3, x_16, x_17, x_18, x_19, lean_box(0));
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.maxEntry!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(318u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
if (lean_obj_tag(x_3) == 0)
{
x_2 = x_3;
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__2;
x_9 = l_panic___rarg(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_maxEntryD___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_maxEntryD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_2) == 0)
{
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minKey_x3f___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_minKey_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
x_2 = lean_box(0);
goto _start;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minKey___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_minKey___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.minKey!", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(341u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
x_2 = x_3;
goto _start;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__2;
x_7 = l_panic___rarg(x_1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
return x_5;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_minKeyD___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_minKeyD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_10, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_2) == 0)
{
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_maxKey_x3f___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
x_2 = lean_box(0);
goto _start;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_maxKey___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_maxKey___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.maxKey!", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(364u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
if (lean_obj_tag(x_3) == 0)
{
x_2 = x_3;
goto _start;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__2;
x_7 = l_panic___rarg(x_1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
return x_5;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_maxKeyD___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_maxKeyD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_nat_dec_lt(x_3, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_3, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_1 = x_8;
x_2 = lean_box(0);
x_3 = x_14;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
else
{
x_1 = x_5;
x_2 = lean_box(0);
x_4 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get(x_1, 4);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_3, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_3, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_nat_sub(x_3, x_21);
lean_dec(x_3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_1 = x_20;
x_2 = lean_box(0);
x_3 = x_26;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_28; 
lean_dec(x_3);
lean_inc(x_19);
lean_inc(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
return x_28;
}
}
else
{
x_1 = x_5;
x_2 = lean_box(0);
x_4 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_entryAtIdx___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_1 = x_6;
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_2, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_2, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_nat_sub(x_2, x_20);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_1 = x_19;
x_2 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
lean_inc(x_18);
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_2);
x_30 = lean_box(0);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.entryAtIdx!", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Out-of-bounds access", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(395u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_nat_dec_lt(x_3, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_3, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_2 = x_7;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_3, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_3, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_nat_sub(x_3, x_20);
lean_dec(x_3);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_2 = x_19;
x_3 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_18);
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_29 = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__3;
x_30 = l_panic___rarg(x_1, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_1 = x_7;
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_2, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_2, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_nat_sub(x_2, x_20);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_1 = x_19;
x_2 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_inc(x_18);
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_entryAtIdxD___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_nat_dec_lt(x_3, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_3, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_1 = x_7;
x_2 = lean_box(0);
x_3 = x_13;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_3);
lean_inc(x_6);
return x_6;
}
}
else
{
x_1 = x_5;
x_2 = lean_box(0);
x_4 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_3, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_3, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_nat_sub(x_3, x_18);
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_1 = x_17;
x_2 = lean_box(0);
x_3 = x_23;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_3);
lean_inc(x_16);
return x_16;
}
}
else
{
x_1 = x_5;
x_2 = lean_box(0);
x_4 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_keyAtIdx___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_nat_dec_lt(x_2, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_2, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_1 = x_5;
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
lean_inc(x_4);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_2, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_2, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_1 = x_16;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_2);
lean_inc(x_15);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_15);
return x_24;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_2);
x_26 = lean_box(0);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.keyAtIdx!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(431u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 4);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_nat_dec_lt(x_3, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_2 = x_6;
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_5);
return x_5;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_3, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_3, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_2 = x_16;
x_3 = x_22;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_15);
return x_15;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_25 = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__2;
x_26 = l_panic___rarg(x_1, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_1 = x_6;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_2);
lean_inc(x_5);
return x_5;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_2, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_2, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_1 = x_16;
x_2 = x_22;
goto _start;
}
else
{
lean_dec(x_2);
lean_inc(x_15);
return x_15;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_keyAtIdxD___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_3 = x_12;
x_4 = x_7;
goto _start;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_8;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_7;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_3 = x_15;
x_4 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = x_8;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_7;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__2;
x_3 = lean_unsigned_to_nat(21u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGED___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryGED___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGTD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryGTD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLED___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryLED___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLTD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getEntryLTD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
switch (x_12) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_box(0);
x_15 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___rarg(x_1, x_3, x_14, x_9);
if (lean_obj_tag(x_15) == 0)
{
return x_13;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
return x_16;
}
}
case 1:
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
default: 
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGE___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_instDecidableEqOrdering(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_box(0);
x_18 = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___rarg(x_1, x_3, x_17, x_9);
if (lean_obj_tag(x_18) == 0)
{
return x_16;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryGT___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
switch (x_12) {
case 0:
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_9;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
case 1:
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_box(0);
x_17 = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___rarg(x_1, x_3, x_16, x_10);
if (lean_obj_tag(x_17) == 0)
{
return x_15;
}
else
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLE___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = 2;
x_14 = l_instDecidableEqOrdering(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_9;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_box(0);
x_18 = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___rarg(x_1, x_3, x_17, x_10);
if (lean_obj_tag(x_18) == 0)
{
return x_16;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getEntryLT___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_3 = x_10;
x_4 = x_6;
goto _start;
}
case 1:
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_7;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_3 = x_11;
x_4 = x_6;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_7;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_dec(x_7);
lean_dec(x_5);
x_4 = x_6;
goto _start;
}
case 1:
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
x_3 = x_12;
x_4 = x_7;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_3 = x_11;
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
x_4 = x_6;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGED___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyGED___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGTD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyGTD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLED___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyLED___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLTD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_getKeyLTD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___rarg(x_1, x_3, x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
return x_7;
}
else
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
}
}
case 1:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
default: 
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_9;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGE___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_instDecidableEqOrdering(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_9;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___rarg(x_1, x_3, x_15, x_8);
if (lean_obj_tag(x_16) == 0)
{
return x_7;
}
else
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyGT___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_dec(x_9);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_8;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
case 1:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
default: 
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___rarg(x_1, x_3, x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
return x_7;
}
else
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLE___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = 2;
x_13 = l_instDecidableEqOrdering(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_8;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___rarg(x_1, x_3, x_15, x_9);
if (lean_obj_tag(x_16) == 0)
{
return x_7;
}
else
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_getKeyLT___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_2) == 0)
{
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_9(x_4, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_3, x_16, x_17, x_18, x_19);
return x_20;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
x_2 = lean_box(0);
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_minEntry___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_10(x_4, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_9, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_5(x_3, x_16, x_17, x_18, x_19, lean_box(0));
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.Const.minEntry!", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(744u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
x_2 = x_3;
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__2;
x_9 = l_panic___rarg(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_minEntryD___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_11, x_12, x_13, x_14, x_15, x_10, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_2) == 0)
{
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_9(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_4(x_3, x_16, x_17, x_18, x_19);
return x_20;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
x_2 = lean_box(0);
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_apply_10(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_5(x_3, x_16, x_17, x_18, x_19, lean_box(0));
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.Const.maxEntry!", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(767u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
if (lean_obj_tag(x_3) == 0)
{
x_2 = x_3;
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__2;
x_9 = l_panic___rarg(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_3) == 0)
{
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_apply_10(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_5(x_4, x_17, x_18, x_19, x_20, x_2);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = lean_apply_1(x_3, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_nat_dec_lt(x_3, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = lean_nat_dec_eq(x_3, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_nat_sub(x_3, x_9);
lean_dec(x_9);
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_box(0), lean_box(0));
x_16 = lean_apply_4(x_15, x_8, lean_box(0), x_14, lean_box(0));
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_18 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_box(0), lean_box(0));
x_19 = lean_apply_4(x_18, x_5, lean_box(0), x_3, lean_box(0));
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_3, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_3, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_20);
x_26 = lean_nat_sub(x_3, x_23);
lean_dec(x_3);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_26, x_27);
lean_dec(x_26);
x_29 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_box(0), lean_box(0));
x_30 = lean_apply_4(x_29, x_22, lean_box(0), x_28, lean_box(0));
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_32 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_box(0), lean_box(0));
x_33 = lean_apply_4(x_32, x_5, lean_box(0), x_3, lean_box(0));
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_1 = x_6;
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_2, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_2, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_nat_sub(x_2, x_20);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_1 = x_19;
x_2 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
lean_inc(x_18);
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_2);
x_30 = lean_box(0);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DTreeMap.Internal.Impl.Const.entryAtIdx!", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1;
x_2 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(798u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_nat_dec_lt(x_3, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_3, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_2 = x_7;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_3, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_3, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_nat_sub(x_3, x_20);
lean_dec(x_3);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_2 = x_19;
x_3 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_18);
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_29 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__2;
x_30 = l_panic___rarg(x_1, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_1 = x_7;
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_2, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_2, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_nat_sub(x_2, x_20);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_1 = x_19;
x_2 = x_25;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_inc(x_18);
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_3 = x_12;
x_4 = x_7;
goto _start;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_8;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_7;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_3 = x_15;
x_4 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_5);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = x_8;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_4 = x_7;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___rarg(x_1, x_3, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4;
x_8 = l_panic___rarg(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___rarg(x_1, x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
switch (x_12) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_box(0);
x_15 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___rarg(x_1, x_3, x_14, x_9);
if (lean_obj_tag(x_15) == 0)
{
return x_13;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
return x_16;
}
}
case 1:
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
default: 
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_instDecidableEqOrdering(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_box(0);
x_18 = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___rarg(x_1, x_3, x_17, x_9);
if (lean_obj_tag(x_18) == 0)
{
return x_16;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
switch (x_12) {
case 0:
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_9;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
case 1:
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_box(0);
x_17 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___rarg(x_1, x_3, x_16, x_10);
if (lean_obj_tag(x_17) == 0)
{
return x_15;
}
else
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_7);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = 2;
x_14 = l_instDecidableEqOrdering(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_9;
x_5 = lean_box(0);
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_box(0);
x_18 = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___rarg(x_1, x_3, x_17, x_10);
if (lean_obj_tag(x_18) == 0)
{
return x_16;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___rarg), 6, 0);
return x_3;
}
}
lean_object* initialize_Init_Data_Nat_Compare(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Internal_Def(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Internal_Balanced(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Internal_Ordered(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Classes_Ord_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Queries(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Compare(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Def(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Balanced(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Ordered(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Classes_Ord_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__3);
l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__4 = _init_l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__4();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_get_x21___rarg___closed__4);
l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_getKey_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_get_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_keysArray___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_minEntry_x21___rarg___closed__3);
l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_minKey_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_maxKey_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___rarg___closed__3);
l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__3 = _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__3();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__3);
l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4 = _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___rarg___closed__4);
l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___rarg___closed__2);
l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__1);
l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
