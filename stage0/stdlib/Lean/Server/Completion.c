// Lean compiler output
// Module: Lean.Server.Completion
// Imports: Lean.Server.Completion.CompletionCollectors Lean.Server.RequestCancellation Std.Data.HashMap
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__35;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__29;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__24;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__33;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__9;
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__32;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t l_Array_foldlMUnsafe_fold___at___Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2690__spec__0___redArg(size_t, size_t, uint64_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Server_Completion_idCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_optionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0(lean_object*, lean_object*);
lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__36;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__6;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instDecidableEqCompletionItemKind___boxed(lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__1(lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__28;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__16;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__1;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__11;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__3;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__34;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__10;
uint64_t l_Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6536_(lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__25;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__21;
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__0(lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__5(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Server_Completion_find_x3f___closed__0;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__31;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__22;
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1175_(uint8_t);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__26;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__30;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__0;
lean_object* l_Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1175____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__17;
extern lean_object* l_Lean_Lsp_instInhabitedCompletionItem;
lean_object* l_instHashableOption___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0___closed__0;
lean_object* l_Lean_Lsp_instDecidableEqCompletionItemTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_hashCompletionItemTag____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1915____boxed(lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0(lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__27;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_instHashableArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__11(lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__19;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Lsp_beqInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1626____boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__8;
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__15;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1716_(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__12;
lean_object* l_Lean_Server_Completion_dotCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6536____boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0___boxed(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instDecidableEqMarkupContent___boxed(lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__7;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_map_go___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__13;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__14;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1716____boxed(lean_object*);
lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__18;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__23;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_map_go___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_8 = lean_array_get(x_1, x_5, x_7);
lean_dec(x_5);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 1, x_8);
x_2 = x_3;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_14 = lean_array_get(x_1, x_11, x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_2);
x_2 = x_15;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_string_dec_eq(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
x_7 = x_14;
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__3(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
x_7 = x_19;
goto block_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__0(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_7 = x_24;
goto block_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__2(x_25, x_27);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
x_7 = x_29;
goto block_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__5(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
x_7 = x_34;
goto block_9;
}
else
{
uint8_t x_35; 
x_35 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__1(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
x_7 = x_35;
goto block_9;
}
}
}
}
}
block_9:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_39; uint64_t x_40; lean_object* x_41; uint64_t x_42; uint64_t x_43; uint64_t x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint64_t x_76; lean_object* x_77; uint64_t x_78; uint64_t x_89; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_array_get_size(x_1);
x_12 = lean_string_hash(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_99; 
x_99 = 11;
x_89 = x_99;
goto block_98;
}
else
{
lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; 
x_100 = lean_ctor_get(x_9, 0);
lean_inc(x_100);
lean_dec(x_9);
x_101 = l_Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1716_(x_100);
lean_dec(x_100);
x_102 = 13;
x_103 = lean_uint64_mix_hash(x_101, x_102);
x_89 = x_103;
goto block_98;
}
block_38:
{
uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_18 = lean_uint64_mix_hash(x_13, x_17);
x_19 = lean_uint64_mix_hash(x_16, x_18);
x_20 = lean_uint64_mix_hash(x_15, x_19);
x_21 = lean_uint64_mix_hash(x_14, x_20);
x_22 = lean_uint64_mix_hash(x_12, x_21);
x_23 = 32;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = 16;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = 1;
x_32 = lean_usize_sub(x_30, x_31);
x_33 = lean_usize_land(x_29, x_32);
x_34 = lean_array_uget(x_1, x_33);
if (lean_is_scalar(x_7)) {
 x_35 = lean_alloc_ctor(1, 3, 0);
} else {
 x_35 = x_7;
}
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_5);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_array_uset(x_1, x_33, x_35);
x_1 = x_36;
x_2 = x_6;
goto _start;
}
block_49:
{
if (lean_obj_tag(x_41) == 0)
{
uint64_t x_44; 
x_44 = 11;
x_13 = x_43;
x_14 = x_39;
x_15 = x_40;
x_16 = x_42;
x_17 = x_44;
goto block_38;
}
else
{
lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6536_(x_45);
lean_dec(x_45);
x_47 = 13;
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_13 = x_43;
x_14 = x_39;
x_15 = x_40;
x_16 = x_42;
x_17 = x_48;
goto block_38;
}
}
block_57:
{
uint64_t x_55; uint64_t x_56; 
x_55 = 13;
x_56 = lean_uint64_mix_hash(x_54, x_55);
x_39 = x_50;
x_40 = x_51;
x_41 = x_52;
x_42 = x_53;
x_43 = x_56;
goto block_49;
}
block_75:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint64_t x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = 11;
x_39 = x_58;
x_40 = x_59;
x_41 = x_63;
x_42 = x_61;
x_43 = x_64;
goto block_49;
}
else
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_67 = 7;
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_array_get_size(x_66);
lean_dec(x_66);
x_70 = lean_nat_dec_lt(x_68, x_69);
if (x_70 == 0)
{
lean_dec(x_69);
x_50 = x_58;
x_51 = x_59;
x_52 = x_65;
x_53 = x_61;
x_54 = x_67;
goto block_57;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_69, x_69);
if (x_71 == 0)
{
lean_dec(x_69);
x_50 = x_58;
x_51 = x_59;
x_52 = x_65;
x_53 = x_61;
x_54 = x_67;
goto block_57;
}
else
{
size_t x_72; size_t x_73; uint64_t x_74; 
x_72 = 0;
x_73 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_74 = l_Array_foldlMUnsafe_fold___at___Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2690__spec__0___redArg(x_72, x_73, x_67);
x_50 = x_58;
x_51 = x_59;
x_52 = x_65;
x_53 = x_61;
x_54 = x_74;
goto block_57;
}
}
}
}
block_88:
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint64_t x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = 11;
x_58 = x_76;
x_59 = x_78;
x_60 = x_80;
x_61 = x_81;
goto block_75;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
x_85 = l_Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1175_(x_84);
x_86 = 13;
x_87 = lean_uint64_mix_hash(x_85, x_86);
x_58 = x_76;
x_59 = x_78;
x_60 = x_82;
x_61 = x_87;
goto block_75;
}
}
block_98:
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_10, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint64_t x_92; 
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
lean_dec(x_10);
x_92 = 11;
x_76 = x_89;
x_77 = x_91;
x_78 = x_92;
goto block_88;
}
else
{
lean_object* x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; 
x_93 = lean_ctor_get(x_10, 1);
lean_inc(x_93);
lean_dec(x_10);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_string_hash(x_94);
lean_dec(x_94);
x_96 = 13;
x_97 = lean_uint64_mix_hash(x_95, x_96);
x_76 = x_89;
x_77 = x_93;
x_78 = x_97;
goto block_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_58; lean_object* x_59; uint64_t x_60; uint64_t x_61; uint64_t x_76; lean_object* x_77; uint64_t x_78; uint64_t x_89; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_array_get_size(x_1);
x_12 = lean_string_hash(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_99; 
x_99 = 11;
x_89 = x_99;
goto block_98;
}
else
{
lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; 
x_100 = lean_ctor_get(x_9, 0);
lean_inc(x_100);
lean_dec(x_9);
x_101 = l_Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1716_(x_100);
lean_dec(x_100);
x_102 = 13;
x_103 = lean_uint64_mix_hash(x_101, x_102);
x_89 = x_103;
goto block_98;
}
block_38:
{
uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_18 = lean_uint64_mix_hash(x_13, x_17);
x_19 = lean_uint64_mix_hash(x_16, x_18);
x_20 = lean_uint64_mix_hash(x_15, x_19);
x_21 = lean_uint64_mix_hash(x_14, x_20);
x_22 = lean_uint64_mix_hash(x_12, x_21);
x_23 = 32;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = 16;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = 1;
x_32 = lean_usize_sub(x_30, x_31);
x_33 = lean_usize_land(x_29, x_32);
x_34 = lean_array_uget(x_1, x_33);
if (lean_is_scalar(x_7)) {
 x_35 = lean_alloc_ctor(1, 3, 0);
} else {
 x_35 = x_7;
}
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_5);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_array_uset(x_1, x_33, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2_spec__2___redArg(x_36, x_6);
return x_37;
}
block_49:
{
if (lean_obj_tag(x_39) == 0)
{
uint64_t x_44; 
x_44 = 11;
x_13 = x_43;
x_14 = x_40;
x_15 = x_41;
x_16 = x_42;
x_17 = x_44;
goto block_38;
}
else
{
lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l_Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6536_(x_45);
lean_dec(x_45);
x_47 = 13;
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_13 = x_43;
x_14 = x_40;
x_15 = x_41;
x_16 = x_42;
x_17 = x_48;
goto block_38;
}
}
block_57:
{
uint64_t x_55; uint64_t x_56; 
x_55 = 13;
x_56 = lean_uint64_mix_hash(x_54, x_55);
x_39 = x_50;
x_40 = x_51;
x_41 = x_52;
x_42 = x_53;
x_43 = x_56;
goto block_49;
}
block_75:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint64_t x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = 11;
x_39 = x_63;
x_40 = x_58;
x_41 = x_60;
x_42 = x_61;
x_43 = x_64;
goto block_49;
}
else
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_67 = 7;
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_array_get_size(x_66);
lean_dec(x_66);
x_70 = lean_nat_dec_lt(x_68, x_69);
if (x_70 == 0)
{
lean_dec(x_69);
x_50 = x_65;
x_51 = x_58;
x_52 = x_60;
x_53 = x_61;
x_54 = x_67;
goto block_57;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_69, x_69);
if (x_71 == 0)
{
lean_dec(x_69);
x_50 = x_65;
x_51 = x_58;
x_52 = x_60;
x_53 = x_61;
x_54 = x_67;
goto block_57;
}
else
{
size_t x_72; size_t x_73; uint64_t x_74; 
x_72 = 0;
x_73 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_74 = l_Array_foldlMUnsafe_fold___at___Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2690__spec__0___redArg(x_72, x_73, x_67);
x_50 = x_65;
x_51 = x_58;
x_52 = x_60;
x_53 = x_61;
x_54 = x_74;
goto block_57;
}
}
}
}
block_88:
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint64_t x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = 11;
x_58 = x_76;
x_59 = x_80;
x_60 = x_78;
x_61 = x_81;
goto block_75;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
x_85 = l_Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1175_(x_84);
x_86 = 13;
x_87 = lean_uint64_mix_hash(x_85, x_86);
x_58 = x_76;
x_59 = x_82;
x_60 = x_78;
x_61 = x_87;
goto block_75;
}
}
block_98:
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_10, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint64_t x_92; 
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
lean_dec(x_10);
x_92 = 11;
x_76 = x_89;
x_77 = x_91;
x_78 = x_92;
goto block_88;
}
else
{
lean_object* x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; 
x_93 = lean_ctor_get(x_10, 1);
lean_inc(x_93);
lean_dec(x_10);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_string_hash(x_94);
lean_dec(x_94);
x_96 = 13;
x_97 = lean_uint64_mix_hash(x_95, x_96);
x_76 = x_89;
x_77 = x_93;
x_78 = x_97;
goto block_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2_spec__2___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
x_7 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0___closed__0;
x_3 = x_7;
goto block_6;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_3 = x_8;
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_11 = x_3;
} else {
 lean_dec_ref(x_3);
 x_11 = lean_box(0);
}
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_string_dec_eq(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_12 = x_24;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__3(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
x_12 = x_29;
goto block_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__0(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
x_12 = x_34;
goto block_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__2(x_35, x_37);
if (x_39 == 0)
{
lean_dec(x_38);
lean_dec(x_36);
x_12 = x_39;
goto block_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__5(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_41);
x_12 = x_44;
goto block_19;
}
else
{
uint8_t x_45; 
x_45 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Lsp_beqCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2520__spec__1(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_12 = x_45;
goto block_19;
}
}
}
}
}
block_19:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg(x_1, x_2, x_10);
if (lean_is_scalar(x_11)) {
 x_14 = lean_alloc_ctor(1, 3, 0);
} else {
 x_14 = x_11;
}
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0(x_1, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_is_scalar(x_11)) {
 x_18 = lean_alloc_ctor(1, 3, 0);
} else {
 x_18 = x_11;
}
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_10);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; lean_object* x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_125; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_21 = x_5;
} else {
 lean_dec_ref(x_5);
 x_21 = lean_box(0);
}
x_22 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
lean_inc(x_22);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_array_get_size(x_20);
x_29 = lean_string_hash(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
uint64_t x_135; 
x_135 = 11;
x_125 = x_135;
goto block_134;
}
else
{
lean_object* x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; 
x_136 = lean_ctor_get(x_26, 0);
lean_inc(x_136);
lean_dec(x_26);
x_137 = l_Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1716_(x_136);
lean_dec(x_136);
x_138 = 13;
x_139 = lean_uint64_mix_hash(x_137, x_138);
x_125 = x_139;
goto block_134;
}
block_74:
{
uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
x_35 = lean_uint64_mix_hash(x_32, x_34);
x_36 = lean_uint64_mix_hash(x_31, x_35);
x_37 = lean_uint64_mix_hash(x_30, x_36);
x_38 = lean_uint64_mix_hash(x_33, x_37);
x_39 = lean_uint64_mix_hash(x_29, x_38);
x_40 = 32;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = 16;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_48 = 1;
x_49 = lean_usize_sub(x_47, x_48);
x_50 = lean_usize_land(x_46, x_49);
x_51 = lean_array_uget(x_20, x_50);
lean_inc(x_51);
lean_inc(x_23);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg(x_23, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_53 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0___closed__0;
x_54 = lean_array_push(x_53, x_22);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_19, x_55);
lean_dec(x_19);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_23);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_51);
x_58 = lean_array_uset(x_20, x_50, x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_56, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(x_58);
if (lean_is_scalar(x_21)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_21;
}
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_65);
x_6 = x_66;
goto block_10;
}
else
{
lean_object* x_67; 
if (lean_is_scalar(x_21)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_21;
}
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_58);
x_6 = x_67;
goto block_10;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_21);
x_68 = lean_box(0);
x_69 = lean_array_uset(x_20, x_50, x_68);
lean_inc(x_23);
x_70 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg(x_22, x_23, x_51);
lean_inc(x_70);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg(x_23, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_19, x_72);
lean_dec(x_19);
x_11 = x_70;
x_12 = x_69;
x_13 = x_50;
x_14 = x_73;
goto block_17;
}
else
{
x_11 = x_70;
x_12 = x_69;
x_13 = x_50;
x_14 = x_19;
goto block_17;
}
}
}
block_85:
{
if (lean_obj_tag(x_75) == 0)
{
uint64_t x_80; 
x_80 = 11;
x_30 = x_77;
x_31 = x_76;
x_32 = x_79;
x_33 = x_78;
x_34 = x_80;
goto block_74;
}
else
{
lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; 
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
lean_dec(x_75);
x_82 = l_Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6536_(x_81);
lean_dec(x_81);
x_83 = 13;
x_84 = lean_uint64_mix_hash(x_82, x_83);
x_30 = x_77;
x_31 = x_76;
x_32 = x_79;
x_33 = x_78;
x_34 = x_84;
goto block_74;
}
}
block_93:
{
uint64_t x_91; uint64_t x_92; 
x_91 = 13;
x_92 = lean_uint64_mix_hash(x_90, x_91);
x_75 = x_86;
x_76 = x_88;
x_77 = x_87;
x_78 = x_89;
x_79 = x_92;
goto block_85;
}
block_111:
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint64_t x_100; 
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_dec(x_94);
x_100 = 11;
x_75 = x_99;
x_76 = x_97;
x_77 = x_95;
x_78 = x_96;
x_79 = x_100;
goto block_85;
}
else
{
lean_object* x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_dec(x_94);
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
lean_dec(x_98);
x_103 = 7;
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_array_get_size(x_102);
lean_dec(x_102);
x_106 = lean_nat_dec_lt(x_104, x_105);
if (x_106 == 0)
{
lean_dec(x_105);
x_86 = x_101;
x_87 = x_95;
x_88 = x_97;
x_89 = x_96;
x_90 = x_103;
goto block_93;
}
else
{
uint8_t x_107; 
x_107 = lean_nat_dec_le(x_105, x_105);
if (x_107 == 0)
{
lean_dec(x_105);
x_86 = x_101;
x_87 = x_95;
x_88 = x_97;
x_89 = x_96;
x_90 = x_103;
goto block_93;
}
else
{
size_t x_108; size_t x_109; uint64_t x_110; 
x_108 = 0;
x_109 = lean_usize_of_nat(x_105);
lean_dec(x_105);
x_110 = l_Array_foldlMUnsafe_fold___at___Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2690__spec__0___redArg(x_108, x_109, x_103);
x_86 = x_101;
x_87 = x_95;
x_88 = x_97;
x_89 = x_96;
x_90 = x_110;
goto block_93;
}
}
}
}
block_124:
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint64_t x_117; 
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = 11;
x_94 = x_116;
x_95 = x_114;
x_96 = x_113;
x_97 = x_117;
goto block_111;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; 
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_dec(x_112);
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
x_121 = l_Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1175_(x_120);
x_122 = 13;
x_123 = lean_uint64_mix_hash(x_121, x_122);
x_94 = x_118;
x_95 = x_114;
x_96 = x_113;
x_97 = x_123;
goto block_111;
}
}
block_134:
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_27, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint64_t x_128; 
x_127 = lean_ctor_get(x_27, 1);
lean_inc(x_127);
lean_dec(x_27);
x_128 = 11;
x_112 = x_127;
x_113 = x_125;
x_114 = x_128;
goto block_124;
}
else
{
lean_object* x_129; lean_object* x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; 
x_129 = lean_ctor_get(x_27, 1);
lean_inc(x_129);
lean_dec(x_27);
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
lean_dec(x_126);
x_131 = lean_string_hash(x_130);
lean_dec(x_130);
x_132 = 13;
x_133 = lean_uint64_mix_hash(x_131, x_132);
x_112 = x_129;
x_113 = x_125;
x_114 = x_133;
goto block_124;
}
}
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_4, x_7);
x_4 = x_8;
x_5 = x_6;
goto _start;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uset(x_12, x_13, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_6 = x_16;
goto block_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_6, x_5);
if (x_20 == 0)
{
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_88; uint64_t x_89; lean_object* x_90; uint64_t x_91; uint64_t x_92; lean_object* x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_114; lean_object* x_115; uint64_t x_116; uint64_t x_127; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_23 = x_7;
} else {
 lean_dec_ref(x_7);
 x_23 = lean_box(0);
}
x_24 = lean_array_uget(x_4, x_6);
lean_inc(x_3);
lean_inc(x_24);
x_25 = lean_apply_1(x_3, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_array_get_size(x_22);
x_31 = lean_string_hash(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
uint64_t x_137; 
x_137 = 11;
x_127 = x_137;
goto block_136;
}
else
{
lean_object* x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; 
x_138 = lean_ctor_get(x_28, 0);
lean_inc(x_138);
lean_dec(x_28);
x_139 = l_Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1716_(x_138);
lean_dec(x_138);
x_140 = 13;
x_141 = lean_uint64_mix_hash(x_139, x_140);
x_127 = x_141;
goto block_136;
}
block_76:
{
uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_37 = lean_uint64_mix_hash(x_35, x_36);
x_38 = lean_uint64_mix_hash(x_34, x_37);
x_39 = lean_uint64_mix_hash(x_32, x_38);
x_40 = lean_uint64_mix_hash(x_33, x_39);
x_41 = lean_uint64_mix_hash(x_31, x_40);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_22, x_52);
lean_inc(x_53);
lean_inc(x_25);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg(x_25, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_55 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0___closed__0;
x_56 = lean_array_push(x_55, x_24);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_21, x_57);
lean_dec(x_21);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_25);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_53);
x_60 = lean_array_uset(x_22, x_52, x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_mul(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(x_60);
if (lean_is_scalar(x_23)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_23;
}
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_8 = x_68;
goto block_12;
}
else
{
lean_object* x_69; 
if (lean_is_scalar(x_23)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_23;
}
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
x_8 = x_69;
goto block_12;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_23);
x_70 = lean_box(0);
x_71 = lean_array_uset(x_22, x_52, x_70);
lean_inc(x_25);
x_72 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg(x_24, x_25, x_53);
lean_inc(x_72);
x_73 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg(x_25, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_sub(x_21, x_74);
lean_dec(x_21);
x_13 = x_72;
x_14 = x_52;
x_15 = x_71;
x_16 = x_75;
goto block_19;
}
else
{
x_13 = x_72;
x_14 = x_52;
x_15 = x_71;
x_16 = x_21;
goto block_19;
}
}
}
block_87:
{
if (lean_obj_tag(x_78) == 0)
{
uint64_t x_82; 
x_82 = 11;
x_32 = x_77;
x_33 = x_79;
x_34 = x_80;
x_35 = x_81;
x_36 = x_82;
goto block_76;
}
else
{
lean_object* x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
lean_dec(x_78);
x_84 = l_Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6536_(x_83);
lean_dec(x_83);
x_85 = 13;
x_86 = lean_uint64_mix_hash(x_84, x_85);
x_32 = x_77;
x_33 = x_79;
x_34 = x_80;
x_35 = x_81;
x_36 = x_86;
goto block_76;
}
}
block_95:
{
uint64_t x_93; uint64_t x_94; 
x_93 = 13;
x_94 = lean_uint64_mix_hash(x_92, x_93);
x_77 = x_88;
x_78 = x_90;
x_79 = x_89;
x_80 = x_91;
x_81 = x_94;
goto block_87;
}
block_113:
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint64_t x_102; 
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
lean_dec(x_96);
x_102 = 11;
x_77 = x_97;
x_78 = x_101;
x_79 = x_98;
x_80 = x_99;
x_81 = x_102;
goto block_87;
}
else
{
lean_object* x_103; lean_object* x_104; uint64_t x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_dec(x_96);
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
lean_dec(x_100);
x_105 = 7;
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_array_get_size(x_104);
lean_dec(x_104);
x_108 = lean_nat_dec_lt(x_106, x_107);
if (x_108 == 0)
{
lean_dec(x_107);
x_88 = x_97;
x_89 = x_98;
x_90 = x_103;
x_91 = x_99;
x_92 = x_105;
goto block_95;
}
else
{
uint8_t x_109; 
x_109 = lean_nat_dec_le(x_107, x_107);
if (x_109 == 0)
{
lean_dec(x_107);
x_88 = x_97;
x_89 = x_98;
x_90 = x_103;
x_91 = x_99;
x_92 = x_105;
goto block_95;
}
else
{
size_t x_110; size_t x_111; uint64_t x_112; 
x_110 = 0;
x_111 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_112 = l_Array_foldlMUnsafe_fold___at___Lean_Lsp_hashCompletionItem____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2690__spec__0___redArg(x_110, x_111, x_105);
x_88 = x_97;
x_89 = x_98;
x_90 = x_103;
x_91 = x_99;
x_92 = x_112;
goto block_95;
}
}
}
}
block_126:
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint64_t x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = 11;
x_96 = x_118;
x_97 = x_116;
x_98 = x_114;
x_99 = x_119;
goto block_113;
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
x_123 = l_Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1175_(x_122);
x_124 = 13;
x_125 = lean_uint64_mix_hash(x_123, x_124);
x_96 = x_120;
x_97 = x_116;
x_98 = x_114;
x_99 = x_125;
goto block_113;
}
}
block_136:
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_29, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint64_t x_130; 
x_129 = lean_ctor_get(x_29, 1);
lean_inc(x_129);
lean_dec(x_29);
x_130 = 11;
x_114 = x_127;
x_115 = x_129;
x_116 = x_130;
goto block_126;
}
else
{
lean_object* x_131; lean_object* x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; 
x_131 = lean_ctor_get(x_29, 1);
lean_inc(x_131);
lean_dec(x_29);
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_string_hash(x_132);
lean_dec(x_132);
x_134 = 13;
x_135 = lean_uint64_mix_hash(x_133, x_134);
x_114 = x_127;
x_115 = x_131;
x_116 = x_135;
goto block_126;
}
}
}
block_12:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___redArg(x_3, x_4, x_5, x_10, x_8);
return x_11;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uset(x_15, x_14, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_8 = x_18;
goto block_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_beqInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1626____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__1;
x_2 = lean_alloc_closure((void*)(l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instDecidableEqCompletionItemKind___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__4;
x_2 = lean_alloc_closure((void*)(l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instDecidableEqCompletionItemTag___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__6;
x_2 = lean_alloc_closure((void*)(l_Array_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__7;
x_2 = lean_alloc_closure((void*)(l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_instDecidableEqMarkupContent___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__9;
x_2 = lean_alloc_closure((void*)(l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__10;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__8;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__11;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__5;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__12;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__3;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__13;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__2;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__14;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__0;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_hashInsertReplaceEdit____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1716____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__17;
x_2 = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__16;
x_2 = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_hashCompletionItemKind____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1175____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__20;
x_2 = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_hashCompletionItemTag____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1915____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__22;
x_2 = l_instHashableArray___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__23;
x_2 = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_hashMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_6536____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__25;
x_2 = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__26;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__24;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__27;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__21;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__28;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__19;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__29;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__18;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__30;
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__16;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__32;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__33;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__34;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__35;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__15;
x_4 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__31;
x_5 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__36;
x_6 = lean_array_size(x_2);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___redArg(x_3, x_4, x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = l_Std_DHashMap_Internal_AssocList_map_go___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(x_1, x_9, x_6);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__11(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 7);
lean_inc(x_4);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0___boxed), 1, 0);
x_3 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Lsp_instInhabitedCompletionItem;
x_7 = lean_array_size(x_5);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10(x_6, x_7, x_8, x_5);
x_10 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_9);
return x_10;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_12, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_9);
return x_10;
}
else
{
size_t x_15; lean_object* x_16; 
x_15 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_16 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12(x_9, x_8, x_15, x_10);
lean_dec(x_9);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__7(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__10(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_array_uget(x_4, x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Server_CancellableT_checkCancelled___at___Lean_Server_CancellableM_checkCancelled_spec__0(x_8, x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_10 = x_32;
x_11 = x_31;
goto block_14;
}
else
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_ctor_get(x_27, 2);
lean_inc(x_33);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_1);
x_37 = l_Lean_Server_Completion_dotCompletion(x_1, x_28, x_35, x_36, x_8, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_10 = x_40;
x_11 = x_39;
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_15 = x_7;
x_16 = x_42;
x_17 = x_41;
goto block_22;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_37;
}
}
case 1:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
x_49 = lean_ctor_get(x_33, 2);
lean_inc(x_49);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_1);
x_50 = l_Lean_Server_Completion_idCompletion(x_1, x_28, x_45, x_49, x_46, x_47, x_44, x_48, x_8, x_43);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_10 = x_53;
x_11 = x_52;
goto block_14;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_15 = x_7;
x_16 = x_55;
x_17 = x_54;
goto block_22;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_dec(x_27);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_33, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_33, 3);
lean_inc(x_60);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_1);
x_61 = l_Lean_Server_Completion_dotIdCompletion(x_1, x_28, x_57, x_59, x_58, x_60, x_8, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_10 = x_64;
x_11 = x_63;
goto block_14;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_15 = x_7;
x_16 = x_66;
x_17 = x_65;
goto block_22;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_61;
}
}
case 3:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_29, 1);
lean_inc(x_67);
lean_dec(x_29);
x_68 = lean_ctor_get(x_27, 1);
lean_inc(x_68);
lean_dec(x_27);
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_33, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_33, 3);
lean_inc(x_71);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_1);
x_72 = l_Lean_Server_Completion_fieldIdCompletion(x_1, x_28, x_68, x_70, x_69, x_71, x_8, x_67);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_10 = x_75;
x_11 = x_74;
goto block_14;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
lean_dec(x_73);
x_15 = x_7;
x_16 = x_77;
x_17 = x_76;
goto block_22;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_72;
}
}
case 5:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_29, 1);
lean_inc(x_78);
lean_dec(x_29);
x_79 = lean_ctor_get(x_27, 1);
lean_inc(x_79);
lean_dec(x_27);
x_80 = lean_ctor_get(x_33, 0);
lean_inc(x_80);
lean_dec(x_33);
lean_inc(x_2);
lean_inc(x_1);
x_81 = l_Lean_Server_Completion_optionCompletion(x_1, x_28, x_79, x_80, x_2, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_15 = x_7;
x_16 = x_82;
x_17 = x_83;
goto block_22;
}
else
{
uint8_t x_84; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 6:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_29, 1);
lean_inc(x_88);
lean_dec(x_29);
x_89 = lean_ctor_get(x_27, 1);
lean_inc(x_89);
lean_dec(x_27);
x_90 = lean_ctor_get(x_33, 1);
lean_inc(x_90);
lean_dec(x_33);
lean_inc(x_2);
lean_inc(x_1);
x_91 = l_Lean_Server_Completion_errorNameCompletion(x_1, x_28, x_89, x_90, x_2, x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_15 = x_7;
x_16 = x_92;
x_17 = x_93;
goto block_22;
}
else
{
uint8_t x_94; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_91);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
case 8:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_33);
x_98 = lean_ctor_get(x_29, 1);
lean_inc(x_98);
lean_dec(x_29);
x_99 = lean_ctor_get(x_27, 1);
lean_inc(x_99);
lean_dec(x_27);
lean_inc(x_1);
x_100 = l_Lean_Server_Completion_tacticCompletion(x_1, x_28, x_99, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_15 = x_7;
x_16 = x_101;
x_17 = x_102;
goto block_22;
}
else
{
uint8_t x_103; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_100);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
default: 
{
lean_object* x_107; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_27);
x_107 = lean_ctor_get(x_29, 1);
lean_inc(x_107);
lean_dec(x_29);
lean_inc(x_3);
x_15 = x_7;
x_16 = x_3;
x_17 = x_107;
goto block_22;
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = l_Array_append___redArg(x_15, x_16);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_18;
x_9 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_4, x_6);
x_14 = lean_array_size(x_13);
x_15 = 0;
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0(x_1, x_2, x_3, x_13, x_14, x_15, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Array_isEmpty___redArg(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
size_t x_21; size_t x_22; 
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_6 = x_22;
x_7 = x_19;
x_9 = x_18;
goto _start;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Server_Completion_find_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_9 = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(x_2, x_3, x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Server_Completion_find_x3f___closed__0;
x_13 = lean_array_size(x_10);
x_14 = 0;
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1(x_1, x_6, x_12, x_10, x_13, x_14, x_12, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_24 = x_16;
} else {
 lean_dec_ref(x_16);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_28 = x_15;
} else {
 lean_dec_ref(x_15);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_30 = x_16;
} else {
 lean_dec_ref(x_16);
 x_30 = lean_box(0);
}
x_31 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(x_29);
lean_dec(x_29);
x_37 = lean_unbox(x_11);
lean_dec(x_11);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_box(1);
x_39 = lean_unbox(x_38);
x_32 = x_39;
goto block_36;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
x_32 = x_41;
goto block_36;
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_28)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_28;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__0(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Server_Completion_find_x3f_spec__1(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
return x_12;
}
}
lean_object* initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_RequestCancellation(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Completion_CompletionCollectors(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_RequestCancellation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0___closed__0 = _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0___closed__0();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_Const_alter___at___Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__6___redArg___lam__0___closed__0);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__0 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__0();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__0);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__1 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__1();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__1);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__2 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__2();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__2);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__3 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__3();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__3);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__4 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__4();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__4);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__5 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__5();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__5);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__6 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__6();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__6);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__7 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__7();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__7);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__8 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__8();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__8);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__9 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__9();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__9);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__10 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__10();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__10);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__11 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__11();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__11);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__12 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__12();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__12);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__13 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__13();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__13);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__14 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__14();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__14);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__15 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__15();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__15);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__16 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__16();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__16);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__17 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__17();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__17);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__18 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__18();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__18);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__19 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__19();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__19);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__20 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__20();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__20);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__21 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__21();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__21);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__22 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__22();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__22);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__23 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__23();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__23);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__24 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__24();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__24);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__25 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__25();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__25);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__26 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__26();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__26);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__27 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__27();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__27);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__28 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__28();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__28);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__29 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__29();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__29);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__30 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__30();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__30);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__31 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__31();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__31);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__32 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__32();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__32);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__33 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__33();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__33);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__34 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__34();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__34);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__35 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__35();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__35);
l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__36 = _init_l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__36();
lean_mark_persistent(l_Array_groupByKey___at_____private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg___closed__36);
l_Lean_Server_Completion_find_x3f___closed__0 = _init_l_Lean_Server_Completion_find_x3f___closed__0();
lean_mark_persistent(l_Lean_Server_Completion_find_x3f___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
