// Lean compiler output
// Module: Lean.Meta.DiscrTree.Basic
// Imports: public import Lean.Meta.DiscrTree.Types public import Lean.CoreM import Init.Data.Range.Polymorphic.Iterators import Init.Omega import Std.Data.HashMap.Basic
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_join(lean_object*);
lean_object* l_List_format___redArg(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l_Array_binInsertM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "noindex"};
static const lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 166, 27, 47, 207, 202, 99, 39)}};
static const lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(lean_object*);
static const lean_array_object l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
static lean_once_cell_t l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_DiscrTree_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_DiscrTree_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isForced___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isForced___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isForced(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isForced___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedForced___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedForced___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedForced(lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Meta.DiscrTree.Basic.0.Lean.Meta.DiscrTree.Trie.forceSlow"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "merged discrimination tree node is lazy"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_force___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_force(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DiscrTree"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Key"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "star"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(8, 3, 45, 254, 183, 37, 206, 62)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "other"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(138, 126, 131, 170, 147, 7, 98, 166)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lit"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(202, 151, 84, 78, 164, 133, 51, 209)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Literal"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(64, 199, 201, 37, 137, 51, 1, 129)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__17_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(68, 214, 249, 146, 84, 160, 212, 27)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fvar"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__20_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value_aux_3),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(191, 195, 92, 248, 246, 94, 216, 42)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "FVarId"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__23 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__23_value;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__24 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__24_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(134, 80, 170, 214, 218, 146, 55, 86)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(246, 212, 153, 136, 172, 214, 179, 96)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__27 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__27_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_2),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value_aux_3),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__27_value),LEAN_SCALAR_PTR_LITERAL(146, 102, 128, 62, 226, 52, 61, 241)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__30 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__30_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value_aux_3),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__30_value),LEAN_SCALAR_PTR_LITERAL(89, 115, 112, 17, 35, 166, 93, 117)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32;
static const lean_string_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__33 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__33_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_2),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value_aux_3),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__33_value),LEAN_SCALAR_PTR_LITERAL(96, 241, 3, 72, 213, 31, 49, 170)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_instToExprKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_instToExprKey___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_object* l_Lean_Meta_DiscrTree_instToExprKey___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToExprKey___closed__1_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___closed__2;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instToExprKey___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instToExprKey___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToExprKey;
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instLTKey;
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instDecidableLtKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKey___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_Key_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Key_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Key_format___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "◾"};
static const lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__2_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Key_format___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__2_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__3_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Key_format___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__4 = (const lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__4_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Key_format___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__4_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__5 = (const lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__5_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Key_format___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__6 = (const lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__6_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Key_format___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__6_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Key_format___closed__7 = (const lean_object*)&l_Lean_Meta_DiscrTree_Key_format___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_instToFormatKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Key_format, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_instToFormatKey___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instToFormatKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DiscrTree_instToFormatKey = (const lean_object*)&l_Lean_Meta_DiscrTree_instToFormatKey___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4;
static lean_once_cell_t l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "chain "};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "node"};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_DiscrTree_format___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_DiscrTree_format___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_format___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<other>"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__3_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "∀ "};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_format_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_format_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Key_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.DiscrTree.Basic.0.Lean.Meta.DiscrTree.Trie.unfold"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_weights_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_weights_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1;
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__1(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1;
static const lean_closure_object l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__3, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__4, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10_value),((lean_object*)&l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__3_value)} };
static const lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.DiscrTree.getEntriesWithKeys"};
static const lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object* v_e_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1));
v___x_6_ = l_Lean_mkAnnotation(v___x_5_, v_e_4_);
return v___x_6_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object* v_e_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1));
v___x_9_ = l_Lean_annotation_x3f(v___x_8_, v_e_7_);
if (lean_obj_tag(v___x_9_) == 0)
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
lean_dec_ref_known(v___x_9_, 1);
v___x_11_ = 1;
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(lean_object* v_e_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_12_);
lean_dec_ref(v_e_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg(){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1));
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___boxed(lean_object* v___dummy_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg();
return v_res_22_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg();
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object* v_00_u03b1_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_26_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg(){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg___boxed(lean_object* v___dummy_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Meta_DiscrTree_instInhabited___redArg();
return v_res_32_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_DiscrTree_instInhabited___redArg();
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object* v_00_u03b1_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___closed__0, &l_Lean_Meta_DiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabited___closed__0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty___redArg(){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty___redArg___boxed(lean_object* v___dummy_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v_res_39_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_empty___closed__0(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty(lean_object* v_00_u03b1_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_once(&l_Lean_Meta_DiscrTree_empty___closed__0, &l_Lean_Meta_DiscrTree_empty___closed__0_once, _init_l_Lean_Meta_DiscrTree_empty___closed__0);
return v___x_42_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isForced___redArg(lean_object* v_x_43_){
_start:
{
switch(lean_obj_tag(v_x_43_))
{
case 2:
{
uint8_t v___x_44_; 
v___x_44_ = 0;
return v___x_44_;
}
case 3:
{
uint8_t v___x_45_; 
v___x_45_ = 0;
return v___x_45_;
}
default: 
{
uint8_t v___x_46_; 
v___x_46_ = 1;
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isForced___redArg___boxed(lean_object* v_x_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Lean_Meta_DiscrTree_Trie_isForced___redArg(v_x_47_);
lean_dec_ref(v_x_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isForced(lean_object* v_00_u03b1_50_, lean_object* v_x_51_){
_start:
{
switch(lean_obj_tag(v_x_51_))
{
case 2:
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
case 3:
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
default: 
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isForced___boxed(lean_object* v_00_u03b1_55_, lean_object* v_x_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Lean_Meta_DiscrTree_Trie_isForced(v_00_u03b1_55_, v_x_56_);
lean_dec_ref(v_x_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedForced___redArg(){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1));
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedForced___redArg___boxed(lean_object* v___dummy_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_DiscrTree_instInhabitedForced___redArg();
return v_res_62_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0(void){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_DiscrTree_instInhabitedForced___redArg();
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedForced(lean_object* v_00_u03b1_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0, &l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg(lean_object* v_ks_68_, lean_object* v_i_69_, lean_object* v_v_70_){
_start:
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = lean_array_get_size(v_ks_68_);
v___x_72_ = lean_nat_dec_lt(v_i_69_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec_ref(v_ks_68_);
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_mk_empty_array_with_capacity(v___x_73_);
v___x_75_ = lean_array_push(v___x_74_, v_v_70_);
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg___closed__0));
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_78_ = lean_array_fget(v_ks_68_, v_i_69_);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_add(v_i_69_, v___x_79_);
v___x_81_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_81_, 0, v_ks_68_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
lean_ctor_set(v___x_81_, 2, v_v_70_);
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_78_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg___boxed(lean_object* v_ks_83_, lean_object* v_i_84_, lean_object* v_v_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg(v_ks_83_, v_i_84_, v_v_85_);
lean_dec(v_i_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix(lean_object* v_00_u03b1_87_, lean_object* v_ks_88_, lean_object* v_i_89_, lean_object* v_v_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg(v_ks_88_, v_i_89_, v_v_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___boxed(lean_object* v_00_u03b1_92_, lean_object* v_ks_93_, lean_object* v_i_94_, lean_object* v_v_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix(v_00_u03b1_92_, v_ks_93_, v_i_94_, v_v_95_);
lean_dec(v_i_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow_spec__0___redArg(lean_object* v_msg_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0, &l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabitedForced___closed__0);
v___x_99_ = lean_panic_fn_borrowed(v___x_98_, v_msg_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow_spec__0(lean_object* v_00_u03b1_100_, lean_object* v_msg_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow_spec__0___redArg(v_msg_101_);
return v___x_102_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__3(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__2));
v___x_107_ = lean_unsigned_to_nat(11u);
v___x_108_ = lean_unsigned_to_nat(51u);
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__1));
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0));
v___x_111_ = l_mkPanicMessageWithDecl(v___x_110_, v___x_109_, v___x_108_, v___x_107_, v___x_106_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(lean_object* v_x_112_){
_start:
{
switch(lean_obj_tag(v_x_112_))
{
case 2:
{
lean_object* v_t_115_; lean_object* v_t_116_; 
v_t_115_ = lean_ctor_get(v_x_112_, 0);
lean_inc_ref(v_t_115_);
lean_dec_ref_known(v_x_112_, 1);
v_t_116_ = lean_thunk_get_own(v_t_115_);
lean_dec_ref(v_t_115_);
switch(lean_obj_tag(v_t_116_))
{
case 2:
{
goto v___jp_117_;
}
case 3:
{
goto v___jp_117_;
}
default: 
{
return v_t_116_;
}
}
v___jp_117_:
{
if (lean_obj_tag(v_t_116_) == 3)
{
lean_object* v_keys_118_; lean_object* v_i_119_; lean_object* v_v_120_; lean_object* v___x_121_; 
v_keys_118_ = lean_ctor_get(v_t_116_, 0);
lean_inc_ref(v_keys_118_);
v_i_119_ = lean_ctor_get(v_t_116_, 1);
lean_inc(v_i_119_);
v_v_120_ = lean_ctor_get(v_t_116_, 2);
lean_inc(v_v_120_);
lean_dec_ref_known(v_t_116_, 3);
v___x_121_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg(v_keys_118_, v_i_119_, v_v_120_);
lean_dec(v_i_119_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_t_116_);
v___x_122_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__3, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__3_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__3);
v___x_123_ = l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow_spec__0___redArg(v___x_122_);
return v___x_123_;
}
}
}
case 3:
{
lean_object* v_keys_124_; lean_object* v_i_125_; lean_object* v_v_126_; lean_object* v___x_127_; 
v_keys_124_ = lean_ctor_get(v_x_112_, 0);
lean_inc_ref(v_keys_124_);
v_i_125_ = lean_ctor_get(v_x_112_, 1);
lean_inc(v_i_125_);
v_v_126_ = lean_ctor_get(v_x_112_, 2);
lean_inc(v_v_126_);
lean_dec_ref_known(v_x_112_, 3);
v___x_127_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg(v_keys_124_, v_i_125_, v_v_126_);
lean_dec(v_i_125_);
return v___x_127_;
}
default: 
{
switch(lean_obj_tag(v_x_112_))
{
case 2:
{
lean_dec_ref_known(v_x_112_, 1);
goto v___jp_113_;
}
case 3:
{
lean_dec_ref_known(v_x_112_, 3);
goto v___jp_113_;
}
default: 
{
return v_x_112_;
}
}
}
}
v___jp_113_:
{
lean_object* v___x_114_; 
v___x_114_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1));
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_object* v_00_u03b1_128_, lean_object* v_x_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_force___redArg(lean_object* v_t_131_){
_start:
{
switch(lean_obj_tag(v_t_131_))
{
case 2:
{
lean_object* v___x_132_; 
v___x_132_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_131_);
return v___x_132_;
}
case 3:
{
lean_object* v___x_133_; 
v___x_133_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_131_);
return v___x_133_;
}
default: 
{
return v_t_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_force(lean_object* v_00_u03b1_134_, lean_object* v_t_135_){
_start:
{
switch(lean_obj_tag(v_t_135_))
{
case 2:
{
lean_object* v___x_136_; 
v___x_136_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_135_);
return v___x_136_;
}
case 3:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_135_);
return v___x_137_;
}
default: 
{
return v_t_135_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_box(0);
v___x_150_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5));
v___x_151_ = l_Lean_mkConst(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_box(0);
v___x_160_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8));
v___x_161_ = l_Lean_mkConst(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_box(0);
v___x_170_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11));
v___x_171_ = l_Lean_mkConst(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_box(0);
v___x_179_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15));
v___x_180_ = l_Lean_mkConst(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_box(0);
v___x_187_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18));
v___x_188_ = l_Lean_mkConst(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_box(0);
v___x_197_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21));
v___x_198_ = l_Lean_mkConst(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_box(0);
v___x_206_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25));
v___x_207_ = l_Lean_mkConst(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_box(0);
v___x_216_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28));
v___x_217_ = l_Lean_mkConst(v___x_216_, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_box(0);
v___x_226_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31));
v___x_227_ = l_Lean_mkConst(v___x_226_, v___x_225_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_box(0);
v___x_236_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34));
v___x_237_ = l_Lean_mkConst(v___x_236_, v___x_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0(lean_object* v_k_238_){
_start:
{
switch(lean_obj_tag(v_k_238_))
{
case 0:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6);
return v___x_239_;
}
case 1:
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9);
return v___x_240_;
}
case 2:
{
lean_object* v_a_241_; lean_object* v___x_242_; 
v_a_241_ = lean_ctor_get(v_k_238_, 0);
lean_inc_ref(v_a_241_);
lean_dec_ref_known(v_k_238_, 1);
v___x_242_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12);
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16);
v___x_244_ = l_Lean_Expr_lit___override(v_a_241_);
v___x_245_ = l_Lean_Expr_app___override(v___x_243_, v___x_244_);
v___x_246_ = l_Lean_Expr_app___override(v___x_242_, v___x_245_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19);
v___x_248_ = l_Lean_Expr_lit___override(v_a_241_);
v___x_249_ = l_Lean_Expr_app___override(v___x_247_, v___x_248_);
v___x_250_ = l_Lean_Expr_app___override(v___x_242_, v___x_249_);
return v___x_250_;
}
}
case 3:
{
lean_object* v_a_251_; lean_object* v_a_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_a_251_ = lean_ctor_get(v_k_238_, 0);
lean_inc(v_a_251_);
v_a_252_ = lean_ctor_get(v_k_238_, 1);
lean_inc(v_a_252_);
lean_dec_ref_known(v_k_238_, 2);
v___x_253_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22);
v___x_254_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26);
v___x_255_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_251_);
v___x_256_ = l_Lean_Expr_app___override(v___x_254_, v___x_255_);
v___x_257_ = l_Lean_mkNatLit(v_a_252_);
v___x_258_ = l_Lean_mkAppB(v___x_253_, v___x_256_, v___x_257_);
return v___x_258_;
}
case 4:
{
lean_object* v_a_259_; lean_object* v_a_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_a_259_ = lean_ctor_get(v_k_238_, 0);
lean_inc(v_a_259_);
v_a_260_ = lean_ctor_get(v_k_238_, 1);
lean_inc(v_a_260_);
lean_dec_ref_known(v_k_238_, 2);
v___x_261_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29);
v___x_262_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_259_);
v___x_263_ = l_Lean_mkNatLit(v_a_260_);
v___x_264_ = l_Lean_mkAppB(v___x_261_, v___x_262_, v___x_263_);
return v___x_264_;
}
case 5:
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32);
return v___x_265_;
}
default: 
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_a_266_ = lean_ctor_get(v_k_238_, 0);
lean_inc(v_a_266_);
v_a_267_ = lean_ctor_get(v_k_238_, 1);
lean_inc(v_a_267_);
v_a_268_ = lean_ctor_get(v_k_238_, 2);
lean_inc(v_a_268_);
lean_dec_ref_known(v_k_238_, 3);
v___x_269_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35);
v___x_270_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_266_);
v___x_271_ = l_Lean_mkNatLit(v_a_267_);
v___x_272_ = l_Lean_mkNatLit(v_a_268_);
v___x_273_ = l_Lean_mkApp3(v___x_269_, v___x_270_, v___x_271_, v___x_272_);
return v___x_273_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__2(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_box(0);
v___x_281_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___closed__1));
v___x_282_ = l_Lean_mkConst(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__3(void){
_start:
{
lean_object* v___x_283_; lean_object* v___f_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___closed__2, &l_Lean_Meta_DiscrTree_instToExprKey___closed__2_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__2);
v___f_284_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___closed__0));
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___f_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___closed__3, &l_Lean_Meta_DiscrTree_instToExprKey___closed__3_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__3);
return v___x_286_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
lean_object* v_k_u2081_290_; lean_object* v_k_u2082_291_; 
switch(lean_obj_tag(v_x_287_))
{
case 2:
{
if (lean_obj_tag(v_x_288_) == 2)
{
lean_object* v_a_295_; lean_object* v_a_296_; uint8_t v___x_297_; 
v_a_295_ = lean_ctor_get(v_x_287_, 0);
v_a_296_ = lean_ctor_get(v_x_288_, 0);
v___x_297_ = l_Lean_Literal_lt(v_a_295_, v_a_296_);
return v___x_297_;
}
else
{
v_k_u2081_290_ = v_x_287_;
v_k_u2082_291_ = v_x_288_;
goto v___jp_289_;
}
}
case 3:
{
if (lean_obj_tag(v_x_288_) == 3)
{
lean_object* v_a_298_; lean_object* v_a_299_; lean_object* v_a_300_; lean_object* v_a_301_; uint8_t v___x_302_; 
v_a_298_ = lean_ctor_get(v_x_287_, 0);
v_a_299_ = lean_ctor_get(v_x_287_, 1);
v_a_300_ = lean_ctor_get(v_x_288_, 0);
v_a_301_ = lean_ctor_get(v_x_288_, 1);
v___x_302_ = l_Lean_Name_quickLt(v_a_298_, v_a_300_);
if (v___x_302_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = l_Lean_instBEqFVarId_beq(v_a_298_, v_a_300_);
if (v___x_303_ == 0)
{
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = lean_nat_dec_lt(v_a_299_, v_a_301_);
return v___x_304_;
}
}
else
{
return v___x_302_;
}
}
else
{
v_k_u2081_290_ = v_x_287_;
v_k_u2082_291_ = v_x_288_;
goto v___jp_289_;
}
}
case 4:
{
if (lean_obj_tag(v_x_288_) == 4)
{
lean_object* v_a_305_; lean_object* v_a_306_; lean_object* v_a_307_; lean_object* v_a_308_; uint8_t v___x_309_; 
v_a_305_ = lean_ctor_get(v_x_287_, 0);
v_a_306_ = lean_ctor_get(v_x_287_, 1);
v_a_307_ = lean_ctor_get(v_x_288_, 0);
v_a_308_ = lean_ctor_get(v_x_288_, 1);
v___x_309_ = l_Lean_Name_quickLt(v_a_305_, v_a_307_);
if (v___x_309_ == 0)
{
uint8_t v___x_310_; 
v___x_310_ = lean_name_eq(v_a_305_, v_a_307_);
if (v___x_310_ == 0)
{
return v___x_310_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_lt(v_a_306_, v_a_308_);
return v___x_311_;
}
}
else
{
return v___x_309_;
}
}
else
{
v_k_u2081_290_ = v_x_287_;
v_k_u2082_291_ = v_x_288_;
goto v___jp_289_;
}
}
case 6:
{
if (lean_obj_tag(v_x_288_) == 6)
{
lean_object* v_a_312_; lean_object* v_a_313_; lean_object* v_a_314_; lean_object* v_a_315_; lean_object* v_a_316_; lean_object* v_a_317_; uint8_t v___x_322_; 
v_a_312_ = lean_ctor_get(v_x_287_, 0);
v_a_313_ = lean_ctor_get(v_x_287_, 1);
v_a_314_ = lean_ctor_get(v_x_287_, 2);
v_a_315_ = lean_ctor_get(v_x_288_, 0);
v_a_316_ = lean_ctor_get(v_x_288_, 1);
v_a_317_ = lean_ctor_get(v_x_288_, 2);
v___x_322_ = l_Lean_Name_quickLt(v_a_312_, v_a_315_);
if (v___x_322_ == 0)
{
uint8_t v___x_323_; 
v___x_323_ = lean_name_eq(v_a_312_, v_a_315_);
if (v___x_323_ == 0)
{
goto v___jp_318_;
}
else
{
uint8_t v___x_324_; 
v___x_324_ = lean_nat_dec_lt(v_a_313_, v_a_316_);
if (v___x_324_ == 0)
{
goto v___jp_318_;
}
else
{
return v___x_324_;
}
}
}
else
{
return v___x_322_;
}
v___jp_318_:
{
uint8_t v___x_319_; 
v___x_319_ = lean_name_eq(v_a_312_, v_a_315_);
if (v___x_319_ == 0)
{
return v___x_319_;
}
else
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_eq(v_a_313_, v_a_316_);
if (v___x_320_ == 0)
{
return v___x_320_;
}
else
{
uint8_t v___x_321_; 
v___x_321_ = lean_nat_dec_lt(v_a_314_, v_a_317_);
return v___x_321_;
}
}
}
}
else
{
v_k_u2081_290_ = v_x_287_;
v_k_u2082_291_ = v_x_288_;
goto v___jp_289_;
}
}
default: 
{
v_k_u2081_290_ = v_x_287_;
v_k_u2082_291_ = v_x_288_;
goto v___jp_289_;
}
}
v___jp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_obj_tag_nat(v_k_u2081_290_);
v___x_293_ = lean_obj_tag_nat(v_k_u2082_291_);
v___x_294_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Lean_Meta_DiscrTree_Key_lt(v_x_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec(v_x_325_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instLTKey(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instDecidableLtKey(lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = l_Lean_Meta_DiscrTree_Key_lt(v_a_330_, v_b_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKey___boxed(lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_Meta_DiscrTree_instDecidableLtKey(v_a_333_, v_b_334_);
lean_dec(v_b_334_);
lean_dec(v_a_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object* v_x_349_){
_start:
{
switch(lean_obj_tag(v_x_349_))
{
case 0:
{
lean_object* v___x_350_; 
v___x_350_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__1));
return v___x_350_;
}
case 1:
{
lean_object* v___x_351_; 
v___x_351_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__3));
return v___x_351_;
}
case 2:
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v_x_349_, 0);
lean_inc_ref(v_a_352_);
lean_dec_ref_known(v_x_349_, 1);
if (lean_obj_tag(v_a_352_) == 0)
{
lean_object* v_val_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_361_; 
v_val_353_ = lean_ctor_get(v_a_352_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_352_);
if (v_isSharedCheck_361_ == 0)
{
v___x_355_ = v_a_352_;
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_val_353_);
lean_dec(v_a_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = l_Nat_reprFast(v_val_353_);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 3);
lean_ctor_set(v___x_355_, 0, v___x_357_);
v___x_359_ = v___x_355_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v_val_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v_val_362_ = lean_ctor_get(v_a_352_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v_a_352_);
if (v_isSharedCheck_370_ == 0)
{
v___x_364_ = v_a_352_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_val_362_);
lean_dec(v_a_352_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = l_String_quote(v_val_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 3);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
case 5:
{
lean_object* v___x_371_; 
v___x_371_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__5));
return v___x_371_;
}
case 6:
{
lean_object* v_a_372_; lean_object* v_a_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_372_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_a_372_);
v_a_373_ = lean_ctor_get(v_x_349_, 1);
lean_inc(v_a_373_);
lean_dec_ref_known(v_x_349_, 3);
v___x_374_ = 1;
v___x_375_ = l_Lean_Name_toString(v_a_372_, v___x_374_);
v___x_376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
v___x_377_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__7));
v___x_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = l_Nat_reprFast(v_a_373_);
v___x_380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_378_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
return v___x_381_;
}
default: 
{
lean_object* v_a_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_382_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_a_382_);
lean_dec(v_x_349_);
v___x_383_ = 1;
v___x_384_ = l_Lean_Name_toString(v_a_382_, v___x_383_);
v___x_385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2));
v___x_394_ = lean_string_length(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4);
v___x_396_ = lean_nat_to_int(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg(lean_object* v_inst_413_, lean_object* v_x_414_){
_start:
{
switch(lean_obj_tag(v_x_414_))
{
case 0:
{
lean_object* v_key_415_; lean_object* v_child_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_438_; 
v_key_415_ = lean_ctor_get(v_x_414_, 0);
v_child_416_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_438_ == 0)
{
v___x_418_ = v_x_414_;
v_isShared_419_ = v_isSharedCheck_438_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_child_416_);
lean_inc(v_key_415_);
lean_dec(v_x_414_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_438_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_420_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1));
v___x_421_ = l_Lean_Meta_DiscrTree_Key_format(v_key_415_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 5);
lean_ctor_set(v___x_418_, 1, v___x_421_);
lean_ctor_set(v___x_418_, 0, v___x_420_);
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_437_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1));
v___x_425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_413_, v_child_416_);
v___x_427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5);
v___x_429_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6));
v___x_430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_427_);
v___x_431_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7));
v___x_432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_428_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = 0;
v___x_435_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set_uint8(v___x_435_, sizeof(void*)*1, v___x_434_);
v___x_436_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*1, v___x_434_);
return v___x_436_;
}
}
}
case 1:
{
lean_object* v_vs_439_; lean_object* v_children_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_475_; 
v_vs_439_ = lean_ctor_get(v_x_414_, 0);
v_children_440_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_475_ == 0)
{
v___x_442_ = v_x_414_;
v_isShared_443_ = v_isSharedCheck_475_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_children_440_);
lean_inc(v_vs_439_);
lean_dec(v_x_414_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_475_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___y_447_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
lean_inc_ref(v_inst_413_);
v___f_444_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0), 2, 1);
lean_closure_set(v___f_444_, 0, v_inst_413_);
v___x_445_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3));
v___x_465_ = lean_array_get_size(v_vs_439_);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_nat_dec_eq(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5));
v___x_469_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__7));
v___x_470_ = lean_array_to_list(v_vs_439_);
v___x_471_ = l_List_format___redArg(v_inst_413_, v___x_470_);
v___x_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_469_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_468_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___y_447_ = v___x_473_;
goto v___jp_446_;
}
else
{
lean_object* v___x_474_; 
lean_dec_ref(v_vs_439_);
lean_dec_ref(v_inst_413_);
v___x_474_ = lean_box(0);
v___y_447_ = v___x_474_;
goto v___jp_446_;
}
v___jp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set_tag(v___x_442_, 5);
lean_ctor_set(v___x_442_, 1, v___y_447_);
lean_ctor_set(v___x_442_, 0, v___x_445_);
v___x_449_ = v___x_442_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___y_447_);
v___x_449_ = v_reuseFailAlloc_464_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_450_ = lean_array_to_list(v_children_440_);
v___x_451_ = lean_box(0);
v___x_452_ = l_List_mapTR_loop___redArg(v___f_444_, v___x_450_, v___x_451_);
v___x_453_ = l_Std_Format_join(v___x_452_);
v___x_454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_449_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5);
v___x_456_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6));
v___x_457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_454_);
v___x_458_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7));
v___x_459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_455_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = 0;
v___x_462_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*1, v___x_461_);
v___x_463_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*1, v___x_461_);
return v___x_463_;
}
}
}
}
case 2:
{
lean_object* v_t_476_; lean_object* v___x_477_; 
v_t_476_ = lean_ctor_get(v_x_414_, 0);
lean_inc_ref(v_t_476_);
lean_dec_ref_known(v_x_414_, 1);
v___x_477_ = lean_thunk_get_own(v_t_476_);
lean_dec_ref(v_t_476_);
v_x_414_ = v___x_477_;
goto _start;
}
default: 
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_x_414_);
v_x_414_ = v___x_479_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0(lean_object* v_inst_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_505_; 
v_fst_483_ = lean_ctor_get(v_x_482_, 0);
v_snd_484_ = lean_ctor_get(v_x_482_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_505_ == 0)
{
v___x_486_ = v_x_482_;
v_isShared_487_ = v_isSharedCheck_505_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snd_484_);
lean_inc(v_fst_483_);
lean_dec(v_x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_505_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_488_ = lean_box(1);
v___x_489_ = l_Lean_Meta_DiscrTree_Key_format(v_fst_483_);
v___x_490_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1));
if (v_isShared_487_ == 0)
{
lean_ctor_set_tag(v___x_486_, 5);
lean_ctor_set(v___x_486_, 1, v___x_490_);
lean_ctor_set(v___x_486_, 0, v___x_489_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_504_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_493_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_481_, v_snd_484_);
v___x_494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5);
v___x_496_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6));
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_494_);
v___x_498_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7));
v___x_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_495_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = 0;
v___x_502_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*1, v___x_501_);
v___x_503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_488_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object* v_00_u03b1_506_, lean_object* v_inst_507_, lean_object* v_x_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_507_, v_x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___redArg(lean_object* v_inst_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format), 3, 2);
lean_closure_set(v___x_511_, 0, lean_box(0));
lean_closure_set(v___x_511_, 1, v_inst_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object* v_00_u03b1_512_, lean_object* v_inst_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format), 3, 2);
lean_closure_set(v___x_514_, 0, lean_box(0));
lean_closure_set(v___x_514_, 1, v_inst_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___redArg___lam__0(lean_object* v_inst_515_, lean_object* v_p_516_, lean_object* v_k_517_, lean_object* v_c_518_){
_start:
{
lean_object* v_fst_519_; lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_549_; 
v_fst_519_ = lean_ctor_get(v_p_516_, 0);
v_snd_520_ = lean_ctor_get(v_p_516_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_p_516_);
if (v_isSharedCheck_549_ == 0)
{
v___x_522_ = v_p_516_;
v_isShared_523_ = v_isSharedCheck_549_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_inc(v_fst_519_);
lean_dec(v_p_516_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_549_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v___x_524_; lean_object* v___y_526_; uint8_t v___x_546_; 
v___x_524_ = 0;
v___x_546_ = lean_unbox(v_fst_519_);
lean_dec(v_fst_519_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(1);
v___y_526_ = v___x_547_;
goto v___jp_525_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_box(0);
v___y_526_ = v___x_548_;
goto v___jp_525_;
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
lean_inc(v___y_526_);
v___x_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_527_, 0, v_snd_520_);
lean_ctor_set(v___x_527_, 1, v___y_526_);
v___x_528_ = l_Lean_Meta_DiscrTree_Key_format(v_k_517_);
v___x_529_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1));
v___x_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_515_, v_c_518_);
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5);
v___x_534_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6));
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_532_);
v___x_536_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7));
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_533_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = 0;
v___x_540_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*1, v___x_539_);
v___x_541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_527_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_box(v___x_524_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_541_);
lean_ctor_set(v___x_522_, 0, v___x_542_);
v___x_544_ = v___x_522_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_541_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___redArg(lean_object* v_inst_554_, lean_object* v_d_555_){
_start:
{
lean_object* v___f_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_snd_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v___f_556_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___redArg___lam__0), 4, 1);
lean_closure_set(v___f_556_, 0, v_inst_554_);
v___x_557_ = ((lean_object*)(l_Lean_Meta_DiscrTree_format___redArg___closed__0));
v___x_558_ = l_Lean_PersistentHashMap_foldl___redArg(v_d_555_, v___f_556_, v___x_557_);
v_snd_559_ = lean_ctor_get(v___x_558_, 1);
lean_inc(v_snd_559_);
lean_dec(v___x_558_);
v___x_560_ = 0;
v___x_561_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_561_, 0, v_snd_559_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format(lean_object* v_00_u03b1_562_, lean_object* v_inst_563_, lean_object* v_d_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Meta_DiscrTree_format___redArg(v_inst_563_, v_d_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormat___redArg(lean_object* v_inst_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format), 3, 2);
lean_closure_set(v___x_567_, 0, lean_box(0));
lean_closure_set(v___x_567_, 1, v_inst_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormat(lean_object* v_00_u03b1_568_, lean_object* v_inst_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format), 3, 2);
lean_closure_set(v___x_570_, 0, lean_box(0));
lean_closure_set(v___x_570_, 1, v_inst_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(lean_object* v_a_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_st_ref_get(v_a_571_);
if (lean_obj_tag(v___x_573_) == 1)
{
lean_object* v_head_574_; lean_object* v_tail_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_head_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_head_574_);
v_tail_575_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_tail_575_);
lean_dec_ref_known(v___x_573_, 2);
v___x_576_ = lean_st_ref_swap(v_a_571_, v_tail_575_);
lean_dec(v___x_576_);
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_head_574_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v___x_573_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg___boxed(lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_581_);
lean_dec(v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f(lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_584_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___boxed(lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f(v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
return v_res_593_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_box(1);
v___x_595_ = l_Lean_MessageData_ofFormat(v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(lean_object* v_as_596_, size_t v_sz_597_, size_t v_i_598_, lean_object* v_b_599_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_usize_dec_lt(v_i_598_, v_sz_597_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v_b_599_);
return v___x_602_;
}
else
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; size_t v___x_607_; size_t v___x_608_; 
v_a_603_ = lean_array_uget_borrowed(v_as_596_, v_i_598_);
v___x_604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v_b_599_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_inc(v_a_603_);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v_a_603_);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_i_598_, v___x_607_);
v_i_598_ = v___x_608_;
v_b_599_ = v___x_606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___boxed(lean_object* v_as_610_, lean_object* v_sz_611_, lean_object* v_i_612_, lean_object* v_b_613_, lean_object* v___y_614_){
_start:
{
size_t v_sz_boxed_615_; size_t v_i_boxed_616_; lean_object* v_res_617_; 
v_sz_boxed_615_ = lean_unbox_usize(v_sz_611_);
lean_dec(v_sz_611_);
v_i_boxed_616_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_as_610_, v_sz_boxed_615_, v_i_boxed_616_, v_b_613_);
lean_dec_ref(v_as_610_);
return v_res_617_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1(void){
_start:
{
lean_object* v___x_619_; lean_object* v_r_620_; 
v___x_619_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0));
v_r_620_ = l_Lean_stringToMessageData(v___x_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(lean_object* v_f_621_, lean_object* v_args_622_, uint8_t v_parenIfNonAtomic_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_array_get_size(v_args_622_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_nat_dec_eq(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v_r_630_; size_t v_sz_631_; size_t v___x_632_; lean_object* v___x_633_; 
v_r_630_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1);
v_sz_631_ = lean_array_size(v_args_622_);
v___x_632_ = ((size_t)0ULL);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_args_622_, v_sz_631_, v___x_632_, v_r_630_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_649_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_649_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_649_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_649_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(2u);
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_a_634_);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v_f_621_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
if (v_parenIfNonAtomic_623_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_641_);
v___x_643_ = v___x_636_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_MessageData_paren(v___x_640_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_645_);
v___x_647_ = v___x_636_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_dec_ref(v_f_621_);
return v___x_633_;
}
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v_f_621_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___boxed(lean_object* v_f_651_, lean_object* v_args_652_, lean_object* v_parenIfNonAtomic_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
uint8_t v_parenIfNonAtomic_boxed_657_; lean_object* v_res_658_; 
v_parenIfNonAtomic_boxed_657_ = lean_unbox(v_parenIfNonAtomic_653_);
v_res_658_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v_f_651_, v_args_652_, v_parenIfNonAtomic_boxed_657_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec_ref(v_args_652_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0(lean_object* v_as_659_, size_t v_sz_660_, size_t v_i_661_, lean_object* v_b_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_as_659_, v_sz_660_, v_i_661_, v_b_662_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___boxed(lean_object* v_as_667_, lean_object* v_sz_668_, lean_object* v_i_669_, lean_object* v_b_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
size_t v_sz_boxed_674_; size_t v_i_boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_668_);
lean_dec(v_sz_668_);
v_i_boxed_675_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0(v_as_667_, v_sz_boxed_674_, v_i_boxed_675_, v_b_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v_as_667_);
return v_res_676_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0, &l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__0);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
lean_ctor_set(v___x_681_, 3, v___x_680_);
lean_ctor_set(v___x_681_, 4, v___x_679_);
lean_ctor_set(v___x_681_, 5, v___x_679_);
lean_ctor_set(v___x_681_, 6, v___x_679_);
lean_ctor_set(v___x_681_, 7, v___x_679_);
lean_ctor_set(v___x_681_, 8, v___x_679_);
lean_ctor_set(v___x_681_, 9, v___x_679_);
lean_ctor_set(v___x_681_, 10, v___x_679_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_unsigned_to_nat(32u);
v___x_683_ = lean_mk_empty_array_with_capacity(v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3(void){
_start:
{
size_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_685_ = ((size_t)5ULL);
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_unsigned_to_nat(32u);
v___x_688_ = lean_mk_empty_array_with_capacity(v___x_687_);
v___x_689_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2);
v___x_690_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___x_688_);
lean_ctor_set(v___x_690_, 2, v___x_686_);
lean_ctor_set(v___x_690_, 3, v___x_686_);
lean_ctor_set_usize(v___x_690_, 4, v___x_685_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = lean_box(1);
v___x_692_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3);
v___x_693_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0);
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_692_);
lean_ctor_set(v___x_694_, 2, v___x_691_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v_toCold_700_; lean_object* v_env_701_; lean_object* v_options_702_; uint8_t v___x_703_; lean_object* v_env_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_699_ = lean_st_ref_get(v___y_697_);
v_toCold_700_ = lean_ctor_get(v___y_696_, 0);
v_env_701_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_env_701_);
lean_dec(v___x_699_);
v_options_702_ = lean_ctor_get(v_toCold_700_, 2);
v___x_703_ = 0;
v_env_704_ = l_Lean_Environment_setRecordingDeps(v_env_701_, v___x_703_);
v___x_705_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1);
v___x_706_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4);
lean_inc_ref(v_options_702_);
v___x_707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_707_, 0, v_env_704_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
lean_ctor_set(v___x_707_, 2, v___x_706_);
lean_ctor_set(v___x_707_, 3, v_options_702_);
v___x_708_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v_msgData_695_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_ref_719_; lean_object* v___x_720_; lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_729_; 
v_ref_719_ = lean_ctor_get(v___y_716_, 2);
v___x_720_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_715_, v___y_716_, v___y_717_);
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_729_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
lean_inc(v_ref_719_);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v_ref_719_);
lean_ctor_set(v___x_725_, 1, v_a_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set_tag(v___x_723_, 1);
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_735_, lean_object* v_msg_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_toCold_741_; lean_object* v_currRecDepth_742_; lean_object* v_ref_743_; uint16_t v_optionFlags_744_; uint8_t v_suppressElabErrors_745_; uint8_t v_checkDeprecated_746_; uint8_t v_isRecordingDeps_747_; lean_object* v_ref_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_toCold_741_ = lean_ctor_get(v___y_738_, 0);
v_currRecDepth_742_ = lean_ctor_get(v___y_738_, 1);
v_ref_743_ = lean_ctor_get(v___y_738_, 2);
v_optionFlags_744_ = lean_ctor_get_uint16(v___y_738_, sizeof(void*)*3);
v_suppressElabErrors_745_ = lean_ctor_get_uint8(v___y_738_, sizeof(void*)*3 + 2);
v_checkDeprecated_746_ = lean_ctor_get_uint8(v___y_738_, sizeof(void*)*3 + 3);
v_isRecordingDeps_747_ = lean_ctor_get_uint8(v___y_738_, sizeof(void*)*3 + 4);
v_ref_748_ = l_Lean_replaceRef(v_ref_735_, v_ref_743_);
lean_inc(v_currRecDepth_742_);
lean_inc_ref(v_toCold_741_);
v___x_749_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_749_, 0, v_toCold_741_);
lean_ctor_set(v___x_749_, 1, v_currRecDepth_742_);
lean_ctor_set(v___x_749_, 2, v_ref_748_);
lean_ctor_set_uint16(v___x_749_, sizeof(void*)*3, v_optionFlags_744_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*3 + 2, v_suppressElabErrors_745_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*3 + 3, v_checkDeprecated_746_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*3 + 4, v_isRecordingDeps_747_);
v___x_750_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_736_, v___x_749_, v___y_739_);
lean_dec_ref_known(v___x_749_, 3);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_751_, lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_751_, v_msg_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec(v_ref_751_);
return v_res_757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__21(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__20));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_791_, lean_object* v_declHint_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_env_797_; uint8_t v___x_798_; 
v___x_795_ = lean_box(0);
v___x_796_ = lean_st_ref_get(v___y_793_);
v_env_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_ref(v_env_797_);
lean_dec(v___x_796_);
v___x_798_ = l_Lean_Name_isAnonymous(v_declHint_792_);
if (v___x_798_ == 0)
{
uint8_t v_isExporting_799_; 
v_isExporting_799_ = lean_ctor_get_uint8(v_env_797_, sizeof(void*)*13);
if (v_isExporting_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v_env_797_);
lean_dec(v_declHint_792_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_msg_791_);
return v___x_800_;
}
else
{
lean_object* v___x_801_; uint8_t v___x_802_; 
lean_inc_ref(v_env_797_);
v___x_801_ = l_Lean_Environment_setExporting(v_env_797_, v___x_798_);
lean_inc(v_declHint_792_);
lean_inc_ref(v___x_801_);
v___x_802_ = l_Lean_Environment_contains(v___x_801_, v_declHint_792_, v_isExporting_799_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v___x_801_);
lean_dec_ref(v_env_797_);
lean_dec(v_declHint_792_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v_msg_791_);
return v___x_803_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_c_809_; lean_object* v___x_810_; 
v___x_804_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1);
v___x_805_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4);
v___x_806_ = l_Lean_Options_empty;
lean_inc_ref(v___x_801_);
v___x_807_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_807_, 0, v___x_801_);
lean_ctor_set(v___x_807_, 1, v___x_804_);
lean_ctor_set(v___x_807_, 2, v___x_805_);
lean_ctor_set(v___x_807_, 3, v___x_806_);
lean_inc(v_declHint_792_);
v___x_808_ = l_Lean_MessageData_ofConstName(v_declHint_792_, v___x_798_);
v_c_809_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_809_, 0, v___x_807_);
lean_ctor_set(v_c_809_, 1, v___x_808_);
v___x_810_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_801_, v_declHint_792_);
lean_dec_ref(v___x_801_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref(v_env_797_);
lean_dec(v_declHint_792_);
v___x_811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_c_809_);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_MessageData_note(v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v_msg_791_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
else
{
lean_object* v_val_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_871_; 
v_val_818_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_871_ == 0)
{
v___x_820_ = v___x_810_;
v_isShared_821_ = v_isSharedCheck_871_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_val_818_);
lean_dec(v___x_810_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_871_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v_modules_823_; lean_object* v_moduleNames_824_; lean_object* v_mod_825_; uint8_t v___x_840_; 
v___x_822_ = l_Lean_Environment_header(v_env_797_);
lean_dec_ref(v_env_797_);
v_modules_823_ = lean_ctor_get(v___x_822_, 3);
lean_inc_ref(v_modules_823_);
v_moduleNames_824_ = lean_ctor_get(v___x_822_, 4);
lean_inc_ref(v_moduleNames_824_);
lean_dec_ref(v___x_822_);
v_mod_825_ = lean_array_get(v___x_795_, v_moduleNames_824_, v_val_818_);
lean_dec_ref(v_moduleNames_824_);
v___x_840_ = l_Lean_isPrivateName(v_declHint_792_);
lean_dec(v_declHint_792_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_array_get_size(v_modules_823_);
v___x_842_ = lean_nat_dec_lt(v_val_818_, v___x_841_);
if (v___x_842_ == 0)
{
lean_dec_ref(v_modules_823_);
lean_dec(v_val_818_);
goto v___jp_826_;
}
else
{
lean_object* v___x_843_; lean_object* v_toImport_844_; uint8_t v_isExported_845_; 
v___x_843_ = lean_array_fget(v_modules_823_, v_val_818_);
lean_dec(v_val_818_);
lean_dec_ref(v_modules_823_);
v_toImport_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc_ref(v_toImport_844_);
lean_dec(v___x_843_);
v_isExported_845_ = lean_ctor_get_uint8(v_toImport_844_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_844_);
if (v_isExported_845_ == 0)
{
goto v___jp_826_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_del_object(v___x_820_);
v___x_846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_c_809_);
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Lean_MessageData_ofName(v_mod_825_);
lean_inc_ref(v___x_850_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_850_);
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_MessageData_note(v___x_856_);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v_msg_791_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec_ref(v_modules_823_);
lean_del_object(v___x_820_);
lean_dec(v_val_818_);
v___x_860_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_c_809_);
v___x_862_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_MessageData_ofName(v_mod_825_);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__21);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_MessageData_note(v___x_867_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v_msg_791_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
v___jp_826_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_c_809_);
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_MessageData_ofName(v_mod_825_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_MessageData_note(v___x_834_);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v_msg_791_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
lean_ctor_set(v___x_820_, 0, v___x_836_);
v___x_838_ = v___x_820_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_872_; 
lean_dec_ref(v_env_797_);
lean_dec(v_declHint_792_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_msg_791_);
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_873_, lean_object* v_declHint_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_873_, v_declHint_874_, v___y_875_);
lean_dec(v___y_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_878_, lean_object* v_declHint_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_894_; 
v___x_884_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_878_, v_declHint_879_, v___y_882_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_894_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_889_ = l_Lean_unknownIdentifierMessageTag;
v___x_890_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_895_, lean_object* v_declHint_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_895_, v_declHint_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_902_, lean_object* v_msg_903_, lean_object* v_declHint_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_911_; 
v___x_909_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_903_, v_declHint_904_, v___y_905_, v___y_906_, v___y_907_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v___x_911_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_902_, v_a_910_, v___y_905_, v___y_906_, v___y_907_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_912_, lean_object* v_msg_913_, lean_object* v_declHint_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_912_, v_msg_913_, v_declHint_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec(v_ref_912_);
return v_res_919_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2));
v___x_925_ = l_Lean_stringToMessageData(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_926_, lean_object* v_constName_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_932_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
v___x_933_ = 0;
lean_inc(v_constName_927_);
v___x_934_ = l_Lean_MessageData_ofConstName(v_constName_927_, v___x_933_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_926_, v___x_937_, v_constName_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_939_, lean_object* v_constName_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_939_, v_constName_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec(v_ref_939_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_ref_951_; lean_object* v___x_952_; 
v_ref_951_ = lean_ctor_get(v___y_948_, 2);
v___x_952_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_951_, v_constName_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(lean_object* v_constName_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v_env_965_; uint8_t v___x_966_; lean_object* v___x_967_; 
v___x_964_ = lean_st_ref_get(v___y_962_);
v_env_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc_ref(v_env_965_);
lean_dec(v___x_964_);
v___x_966_ = 0;
lean_inc(v_constName_959_);
v___x_967_ = l_Lean_Environment_findConstVal_x3f(v_env_965_, v_constName_959_, v___x_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_959_, v___y_960_, v___y_961_, v___y_962_);
return v___x_968_;
}
else
{
lean_object* v_val_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_constName_959_);
v_val_969_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_967_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_val_969_);
lean_dec(v___x_967_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 0);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_val_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0___boxed(lean_object* v_constName_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
if (lean_obj_tag(v_a_983_) == 0)
{
lean_object* v___x_985_; 
v___x_985_ = l_List_reverse___redArg(v_a_984_);
return v___x_985_;
}
else
{
lean_object* v_head_986_; lean_object* v_tail_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_996_; 
v_head_986_ = lean_ctor_get(v_a_983_, 0);
v_tail_987_ = lean_ctor_get(v_a_983_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_a_983_);
if (v_isSharedCheck_996_ == 0)
{
v___x_989_ = v_a_983_;
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_tail_987_);
lean_inc(v_head_986_);
lean_dec(v_a_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_mkLevelParam(v_head_986_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v_a_984_);
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_a_984_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
v_a_983_ = v_tail_987_;
v_a_984_ = v___x_993_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(lean_object* v_constName_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
lean_inc(v_constName_997_);
v___x_1002_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1014_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1014_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1014_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_levelParams_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v_levelParams_1007_ = lean_ctor_get(v_a_1003_, 1);
lean_inc(v_levelParams_1007_);
lean_dec(v_a_1003_);
v___x_1008_ = lean_box(0);
v___x_1009_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(v_levelParams_1007_, v___x_1008_);
v___x_1010_ = l_Lean_mkConst(v_constName_997_, v___x_1009_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1010_);
v___x_1012_ = v___x_1005_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_constName_997_);
v_a_1015_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1002_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1002_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0___boxed(lean_object* v_constName_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_constName_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
return v_res_1028_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1));
v___x_1035_ = l_Lean_MessageData_ofFormat(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4));
v___x_1040_ = l_Lean_MessageData_ofFormat(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__6));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(uint8_t v_parenIfNonAtomic_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_1047_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1170_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1170_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1170_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
if (lean_obj_tag(v_a_1052_) == 1)
{
lean_object* v_val_1056_; 
v_val_1056_ = lean_ctor_get(v_a_1052_, 0);
lean_inc(v_val_1056_);
lean_dec_ref_known(v_a_1052_, 1);
switch(lean_obj_tag(v_val_1056_))
{
case 0:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
case 1:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1061_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1061_);
v___x_1063_ = v___x_1054_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
case 2:
{
lean_object* v_a_1065_; 
v_a_1065_ = lean_ctor_get(v_val_1056_, 0);
lean_inc_ref(v_a_1065_);
lean_dec_ref_known(v_val_1056_, 1);
if (lean_obj_tag(v_a_1065_) == 0)
{
lean_object* v_val_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1078_; 
v_val_1066_ = lean_ctor_get(v_a_1065_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_a_1065_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1068_ = v_a_1065_;
v_isShared_1069_ = v_isSharedCheck_1078_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_val_1066_);
lean_dec(v_a_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1078_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = l_Nat_reprFast(v_val_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 3);
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = l_Lean_MessageData_ofFormat(v___x_1072_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1073_);
v___x_1075_ = v___x_1054_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v_val_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v_val_1079_ = lean_ctor_get(v_a_1065_, 0);
lean_inc_ref(v_val_1079_);
lean_dec_ref_known(v_a_1065_, 1);
v___x_1080_ = l_Lean_stringToMessageData(v_val_1079_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1080_);
v___x_1082_ = v___x_1054_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
case 3:
{
lean_object* v_a_1084_; lean_object* v_a_1085_; lean_object* v___x_1086_; 
lean_del_object(v___x_1054_);
v_a_1084_ = lean_ctor_get(v_val_1056_, 0);
lean_inc(v_a_1084_);
v_a_1085_ = lean_ctor_get(v_val_1056_, 1);
lean_inc(v_a_1085_);
lean_dec_ref_known(v_val_1056_, 2);
v___x_1086_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_1085_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = l_Lean_mkFVar(v_a_1084_);
v___x_1089_ = l_Lean_MessageData_ofExpr(v___x_1088_);
v___x_1090_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_1089_, v_a_1087_, v_parenIfNonAtomic_1046_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1087_);
return v___x_1090_;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_1084_);
v_a_1091_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1086_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1086_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
case 4:
{
lean_object* v_a_1099_; lean_object* v_a_1100_; lean_object* v___x_1101_; 
lean_del_object(v___x_1054_);
v_a_1099_ = lean_ctor_get(v_val_1056_, 0);
lean_inc(v_a_1099_);
v_a_1100_ = lean_ctor_get(v_val_1056_, 1);
lean_inc(v_a_1100_);
lean_dec_ref_known(v_val_1056_, 2);
v___x_1101_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_a_1099_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1103_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_1100_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1100_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = l_Lean_MessageData_ofExpr(v_a_1102_);
v___x_1106_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_1105_, v_a_1104_, v_parenIfNonAtomic_1046_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1104_);
return v___x_1106_;
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v_a_1102_);
v_a_1107_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1103_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1103_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_a_1100_);
v_a_1115_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1101_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1101_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
case 5:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_del_object(v___x_1054_);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v___x_1123_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___x_1126_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7);
v___x_1127_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_1126_, v_a_1125_, v_parenIfNonAtomic_1046_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1125_);
return v___x_1127_;
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1124_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1124_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
default: 
{
lean_object* v_a_1136_; lean_object* v_a_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; 
lean_del_object(v___x_1054_);
v_a_1136_ = lean_ctor_get(v_val_1056_, 1);
lean_inc(v_a_1136_);
v_a_1137_ = lean_ctor_get(v_val_1056_, 2);
lean_inc(v_a_1137_);
lean_dec_ref_known(v_val_1056_, 3);
v___x_1138_ = 1;
v___x_1139_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1138_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1165_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1165_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1165_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; 
v___x_1144_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_1137_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1137_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_a_1140_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_add(v_a_1136_, v___x_1148_);
lean_dec(v_a_1136_);
v___x_1150_ = l_Nat_reprFast(v___x_1149_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 3);
lean_ctor_set(v___x_1142_, 0, v___x_1150_);
v___x_1152_ = v___x_1142_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_MessageData_ofFormat(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1147_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_1154_, v_a_1145_, v_parenIfNonAtomic_1046_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1145_);
return v___x_1155_;
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
lean_dec(v_a_1136_);
v_a_1157_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1144_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1144_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
else
{
lean_dec(v_a_1137_);
lean_dec(v_a_1136_);
return v___x_1139_;
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_dec(v_a_1052_);
v___x_1166_ = l_Lean_MessageData_nil;
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1166_);
v___x_1168_ = v___x_1054_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1051_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1051_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(lean_object* v_upperBound_1179_, lean_object* v_a_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_nat_dec_lt(v_a_1180_, v_upperBound_1179_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
lean_dec(v_a_1180_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_b_1181_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1186_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = lean_array_push(v_b_1181_, v_a_1189_);
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_a_1180_, v___x_1191_);
lean_dec(v_a_1180_);
v_a_1180_ = v___x_1192_;
v_b_1181_ = v___x_1190_;
goto _start;
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_b_1181_);
lean_dec(v_a_1180_);
v_a_1194_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1188_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1188_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(lean_object* v_num_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v_r_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v_r_1208_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0));
v___x_1209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_num_1202_, v___x_1207_, v_r_1208_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___boxed(lean_object* v_num_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_num_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec(v_num_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg___boxed(lean_object* v_upperBound_1216_, lean_object* v_a_1217_, lean_object* v_b_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_1216_, v_a_1217_, v_b_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec(v_upperBound_1216_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___boxed(lean_object* v_parenIfNonAtomic_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
uint8_t v_parenIfNonAtomic_boxed_1229_; lean_object* v_res_1230_; 
v_parenIfNonAtomic_boxed_1229_ = lean_unbox(v_parenIfNonAtomic_1224_);
v_res_1230_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v_parenIfNonAtomic_boxed_1229_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(lean_object* v_upperBound_1231_, lean_object* v_inst_1232_, lean_object* v_R_1233_, lean_object* v_a_1234_, lean_object* v_b_1235_, lean_object* v_c_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_1231_, v_a_1234_, v_b_1235_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___boxed(lean_object* v_upperBound_1242_, lean_object* v_inst_1243_, lean_object* v_R_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_, lean_object* v_c_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(v_upperBound_1242_, v_inst_1243_, v_R_1244_, v_a_1245_, v_b_1246_, v_c_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v_upperBound_1242_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1253_, lean_object* v_constName_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_constName_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(v_00_u03b1_1260_, v_constName_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_1267_, lean_object* v_ref_1268_, lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1268_, v_constName_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_ref_1276_, lean_object* v_constName_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_1275_, v_ref_1276_, v_constName_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v_ref_1276_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1283_, lean_object* v_ref_1284_, lean_object* v_msg_1285_, lean_object* v_declHint_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1284_, v_msg_1285_, v_declHint_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_ref_1293_, lean_object* v_msg_1294_, lean_object* v_declHint_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_1292_, v_ref_1293_, v_msg_1294_, v_declHint_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec(v_ref_1293_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_1301_, lean_object* v_declHint_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1301_, v_declHint_1302_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_1308_, lean_object* v_declHint_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_1308_, v_declHint_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1315_, lean_object* v_ref_1316_, lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_1316_, v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1323_, lean_object* v_ref_1324_, lean_object* v_msg_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1323_, v_ref_1324_, v_msg_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec(v_ref_1324_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_1331_, lean_object* v_msg_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1332_, v___y_1334_, v___y_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_msg_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_1338_, v_msg_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern(lean_object* v_keys_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1349_ = 0;
v___x_1350_ = lean_array_to_list(v_keys_1345_);
v___x_1351_ = lean_st_mk_ref(v___x_1350_);
v___x_1352_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1349_, v___x_1351_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_st_ref_get(v___x_1351_);
lean_dec(v___x_1351_);
lean_dec(v___x_1357_);
if (v_isShared_1356_ == 0)
{
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1353_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_dec(v___x_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern___boxed(lean_object* v_keys_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object* v_keys_1367_, lean_object* v_v_1368_, lean_object* v_i_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1370_, 0, v_keys_1367_);
lean_ctor_set(v___x_1370_, 1, v_i_1369_);
lean_ctor_set(v___x_1370_, 2, v_v_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object* v_00_u03b1_1371_, lean_object* v_keys_1372_, lean_object* v_v_1373_, lean_object* v_i_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1375_, 0, v_keys_1372_);
lean_ctor_set(v___x_1375_, 1, v_i_1374_);
lean_ctor_set(v___x_1375_, 2, v_v_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(lean_object* v_inst_1376_, lean_object* v_vs_1377_, lean_object* v_v_1378_, lean_object* v_i_1379_){
_start:
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_array_get_size(v_vs_1377_);
v___x_1381_ = lean_nat_dec_lt(v_i_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec(v_i_1379_);
lean_dec_ref(v_inst_1376_);
v___x_1382_ = lean_array_push(v_vs_1377_, v_v_1378_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1383_ = lean_array_fget_borrowed(v_vs_1377_, v_i_1379_);
lean_inc_ref(v_inst_1376_);
lean_inc(v___x_1383_);
lean_inc(v_v_1378_);
v___x_1384_ = lean_apply_2(v_inst_1376_, v_v_1378_, v___x_1383_);
v___x_1385_ = lean_unbox(v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_nat_add(v_i_1379_, v___x_1386_);
lean_dec(v_i_1379_);
v_i_1379_ = v___x_1387_;
goto _start;
}
else
{
lean_object* v___x_1389_; 
lean_dec_ref(v_inst_1376_);
v___x_1389_ = lean_array_fset(v_vs_1377_, v_i_1379_, v_v_1378_);
lean_dec(v_i_1379_);
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop(lean_object* v_00_u03b1_1390_, lean_object* v_inst_1391_, lean_object* v_vs_1392_, lean_object* v_v_1393_, lean_object* v_i_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(v_inst_1391_, v_vs_1392_, v_v_1393_, v_i_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(lean_object* v_inst_1396_, lean_object* v_vs_1397_, lean_object* v_v_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(v_inst_1396_, v_vs_1397_, v_v_1398_, v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal(lean_object* v_00_u03b1_1401_, lean_object* v_inst_1402_, lean_object* v_vs_1403_, lean_object* v_v_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_1402_, v_vs_1403_, v_v_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(lean_object* v_a_1406_, lean_object* v_b_1407_){
_start:
{
lean_object* v_fst_1408_; lean_object* v_fst_1409_; uint8_t v___x_1410_; 
v_fst_1408_ = lean_ctor_get(v_a_1406_, 0);
v_fst_1409_ = lean_ctor_get(v_b_1407_, 0);
v___x_1410_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1408_, v_fst_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed(lean_object* v_a_1411_, lean_object* v_b_1412_){
_start:
{
uint8_t v_res_1413_; lean_object* v_r_1414_; 
v_res_1413_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(v_a_1411_, v_b_1412_);
lean_dec_ref(v_b_1412_);
lean_dec_ref(v_a_1411_);
v_r_1414_ = lean_box(v_res_1413_);
return v_r_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(lean_object* v___x_1415_, lean_object* v_x_1416_){
_start:
{
lean_inc_ref(v___x_1415_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed(lean_object* v___x_1417_, lean_object* v_x_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(v___x_1417_, v_x_1418_);
lean_dec_ref(v_x_1418_);
lean_dec_ref(v___x_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(lean_object* v___x_1420_, lean_object* v_x_1421_){
_start:
{
lean_inc_ref(v___x_1420_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed(lean_object* v___x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(v___x_1422_, v_x_1423_);
lean_dec_ref(v___x_1422_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4(lean_object* v_i_1425_, lean_object* v_keys_1426_, lean_object* v_v_1427_, lean_object* v_k_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_c_1432_; lean_object* v___x_1433_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_nat_add(v_i_1425_, v___x_1430_);
v_c_1432_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_c_1432_, 0, v_keys_1426_);
lean_ctor_set(v_c_1432_, 1, v___x_1431_);
lean_ctor_set(v_c_1432_, 2, v_v_1427_);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_k_1428_);
lean_ctor_set(v___x_1433_, 1, v_c_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4___boxed(lean_object* v_i_1434_, lean_object* v_keys_1435_, lean_object* v_v_1436_, lean_object* v_k_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4(v_i_1434_, v_keys_1435_, v_v_1436_, v_k_1437_, v_x_1438_);
lean_dec(v_i_1434_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3___boxed(lean_object* v_i_1460_, lean_object* v_inst_1461_, lean_object* v_keys_1462_, lean_object* v_v_1463_, lean_object* v_k_1464_, lean_object* v_x_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3(v_i_1460_, v_inst_1461_, v_keys_1462_, v_v_1463_, v_k_1464_, v_x_1465_);
lean_dec(v_i_1460_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(lean_object* v_inst_1467_, lean_object* v_keys_1468_, lean_object* v_v_1469_, lean_object* v_i_1470_, lean_object* v_t_1471_){
_start:
{
lean_object* v___f_1472_; lean_object* v___x_1473_; lean_object* v_val_1475_; 
v___f_1472_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0));
v___x_1473_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
switch(lean_obj_tag(v_t_1471_))
{
case 2:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_1471_);
v_val_1475_ = v___x_1535_;
goto v___jp_1474_;
}
case 3:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_1471_);
v_val_1475_ = v___x_1536_;
goto v___jp_1474_;
}
default: 
{
v_val_1475_ = v_t_1471_;
goto v___jp_1474_;
}
}
v___jp_1474_:
{
if (lean_obj_tag(v_val_1475_) == 0)
{
lean_object* v_key_1476_; lean_object* v_child_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1513_; 
v_key_1476_ = lean_ctor_get(v_val_1475_, 0);
v_child_1477_ = lean_ctor_get(v_val_1475_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_val_1475_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1479_ = v_val_1475_;
v_isShared_1480_ = v_isSharedCheck_1513_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_child_1477_);
lean_inc(v_key_1476_);
lean_dec(v_val_1475_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1513_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = lean_array_get_size(v_keys_1468_);
v___x_1482_ = lean_nat_dec_lt(v_i_1470_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
lean_dec(v_i_1470_);
lean_dec_ref(v_keys_1468_);
lean_dec_ref(v_inst_1467_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = lean_mk_empty_array_with_capacity(v___x_1483_);
lean_inc_ref(v___x_1484_);
v___x_1485_ = lean_array_push(v___x_1484_, v_v_1469_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_key_1476_);
lean_ctor_set(v___x_1486_, 1, v_child_1477_);
v___x_1487_ = lean_array_push(v___x_1484_, v___x_1486_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set_tag(v___x_1479_, 1);
lean_ctor_set(v___x_1479_, 1, v___x_1487_);
lean_ctor_set(v___x_1479_, 0, v___x_1485_);
v___x_1489_ = v___x_1479_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
else
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_array_fget_borrowed(v_keys_1468_, v_i_1470_);
v___x_1492_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_1491_, v_key_1476_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___f_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_inc(v___x_1491_);
lean_dec_ref(v_inst_1467_);
v___x_1493_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_key_1476_);
lean_ctor_set(v___x_1494_, 1, v_child_1477_);
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_mk_empty_array_with_capacity(v___x_1495_);
v___x_1497_ = lean_array_push(v___x_1496_, v___x_1494_);
v___x_1498_ = lean_nat_add(v_i_1470_, v___x_1495_);
lean_dec(v_i_1470_);
v___x_1499_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1499_, 0, v_keys_1468_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
lean_ctor_set(v___x_1499_, 2, v_v_1469_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1491_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
lean_inc_ref_n(v___x_1500_, 2);
v___f_1501_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1501_, 0, v___x_1500_);
v___f_1502_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1502_, 0, v___x_1500_);
v___x_1503_ = l_Array_binInsertM___redArg(v___x_1473_, v___f_1472_, v___f_1501_, v___f_1502_, v___x_1497_, v___x_1500_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set_tag(v___x_1479_, 1);
lean_ctor_set(v___x_1479_, 1, v___x_1503_);
lean_ctor_set(v___x_1479_, 0, v___x_1493_);
v___x_1505_ = v___x_1479_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1507_ = lean_unsigned_to_nat(1u);
v___x_1508_ = lean_nat_add(v_i_1470_, v___x_1507_);
lean_dec(v_i_1470_);
v___x_1509_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1467_, v_keys_1468_, v_v_1469_, v___x_1508_, v_child_1477_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v___x_1509_);
v___x_1511_ = v___x_1479_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_key_1476_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
else
{
lean_object* v_vs_1514_; lean_object* v_children_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1534_; 
v_vs_1514_ = lean_ctor_get(v_val_1475_, 0);
v_children_1515_ = lean_ctor_get(v_val_1475_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_val_1475_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1517_ = v_val_1475_;
v_isShared_1518_ = v_isSharedCheck_1534_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_children_1515_);
lean_inc(v_vs_1514_);
lean_dec(v_val_1475_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1534_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = lean_array_get_size(v_keys_1468_);
v___x_1520_ = lean_nat_dec_lt(v_i_1470_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
lean_dec(v_i_1470_);
lean_dec_ref(v_keys_1468_);
v___x_1521_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_1467_, v_vs_1514_, v_v_1469_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1521_);
v___x_1523_ = v___x_1517_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_children_1515_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
else
{
lean_object* v_k_1525_; lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_c_1530_; lean_object* v___x_1532_; 
v_k_1525_ = lean_array_fget(v_keys_1468_, v_i_1470_);
lean_inc_n(v_k_1525_, 2);
lean_inc(v_v_1469_);
lean_inc_ref(v_keys_1468_);
lean_inc(v_i_1470_);
v___f_1526_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_1526_, 0, v_i_1470_);
lean_closure_set(v___f_1526_, 1, v_inst_1467_);
lean_closure_set(v___f_1526_, 2, v_keys_1468_);
lean_closure_set(v___f_1526_, 3, v_v_1469_);
lean_closure_set(v___f_1526_, 4, v_k_1525_);
v___f_1527_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_1527_, 0, v_i_1470_);
lean_closure_set(v___f_1527_, 1, v_keys_1468_);
lean_closure_set(v___f_1527_, 2, v_v_1469_);
lean_closure_set(v___f_1527_, 3, v_k_1525_);
v___x_1528_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1));
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_k_1525_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v_c_1530_ = l_Array_binInsertM___redArg(v___x_1473_, v___f_1472_, v___f_1526_, v___f_1527_, v_children_1515_, v___x_1529_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 1, v_c_1530_);
v___x_1532_ = v___x_1517_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_vs_1514_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_c_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3(lean_object* v_i_1537_, lean_object* v_inst_1538_, lean_object* v_keys_1539_, lean_object* v_v_1540_, lean_object* v_k_1541_, lean_object* v_x_1542_){
_start:
{
lean_object* v_snd_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1553_; 
v_snd_1543_ = lean_ctor_get(v_x_1542_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_x_1542_, 0);
lean_dec(v_unused_1554_);
v___x_1545_ = v_x_1542_;
v_isShared_1546_ = v_isSharedCheck_1553_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_snd_1543_);
lean_dec(v_x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1553_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v_c_1549_; lean_object* v___x_1551_; 
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_i_1537_, v___x_1547_);
v_c_1549_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1538_, v_keys_1539_, v_v_1540_, v___x_1548_, v_snd_1543_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v_c_1549_);
lean_ctor_set(v___x_1545_, 0, v_k_1541_);
v___x_1551_ = v___x_1545_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_k_1541_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_c_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux(lean_object* v_00_u03b1_1555_, lean_object* v_inst_1556_, lean_object* v_keys_1557_, lean_object* v_v_1558_, lean_object* v_i_1559_, lean_object* v_t_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1556_, v_keys_1557_, v_v_1558_, v_i_1559_, v_t_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux_match__1_splitter___redArg(lean_object* v_x_1562_, lean_object* v_h__1_1563_, lean_object* v_h__2_1564_){
_start:
{
if (lean_obj_tag(v_x_1562_) == 0)
{
lean_object* v_key_1565_; lean_object* v_child_1566_; lean_object* v___x_1567_; 
lean_dec(v_h__2_1564_);
v_key_1565_ = lean_ctor_get(v_x_1562_, 0);
lean_inc(v_key_1565_);
v_child_1566_ = lean_ctor_get(v_x_1562_, 1);
lean_inc_ref(v_child_1566_);
lean_dec_ref_known(v_x_1562_, 2);
v___x_1567_ = lean_apply_3(v_h__1_1563_, v_key_1565_, v_child_1566_, lean_box(0));
return v___x_1567_;
}
else
{
lean_object* v_vs_1568_; lean_object* v_children_1569_; lean_object* v___x_1570_; 
lean_dec(v_h__1_1563_);
v_vs_1568_ = lean_ctor_get(v_x_1562_, 0);
lean_inc_ref(v_vs_1568_);
v_children_1569_ = lean_ctor_get(v_x_1562_, 1);
lean_inc_ref(v_children_1569_);
lean_dec_ref_known(v_x_1562_, 2);
v___x_1570_ = lean_apply_3(v_h__2_1564_, v_vs_1568_, v_children_1569_, lean_box(0));
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux_match__1_splitter(lean_object* v_00_u03b1_1571_, lean_object* v_motive_1572_, lean_object* v_x_1573_, lean_object* v_h__1_1574_, lean_object* v_h__2_1575_){
_start:
{
if (lean_obj_tag(v_x_1573_) == 0)
{
lean_object* v_key_1576_; lean_object* v_child_1577_; lean_object* v___x_1578_; 
lean_dec(v_h__2_1575_);
v_key_1576_ = lean_ctor_get(v_x_1573_, 0);
lean_inc(v_key_1576_);
v_child_1577_ = lean_ctor_get(v_x_1573_, 1);
lean_inc_ref(v_child_1577_);
lean_dec_ref_known(v_x_1573_, 2);
v___x_1578_ = lean_apply_3(v_h__1_1574_, v_key_1576_, v_child_1577_, lean_box(0));
return v___x_1578_;
}
else
{
lean_object* v_vs_1579_; lean_object* v_children_1580_; lean_object* v___x_1581_; 
lean_dec(v_h__1_1574_);
v_vs_1579_ = lean_ctor_get(v_x_1573_, 0);
lean_inc_ref(v_vs_1579_);
v_children_1580_ = lean_ctor_get(v_x_1573_, 1);
lean_inc_ref(v_children_1580_);
lean_dec_ref_known(v_x_1573_, 2);
v___x_1581_ = lean_apply_3(v_h__2_1575_, v_vs_1579_, v_children_1580_, lean_box(0));
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_format_match__1_splitter___redArg(lean_object* v_x_1582_, lean_object* v_h__1_1583_){
_start:
{
lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1586_; 
v_fst_1584_ = lean_ctor_get(v_x_1582_, 0);
lean_inc(v_fst_1584_);
v_snd_1585_ = lean_ctor_get(v_x_1582_, 1);
lean_inc(v_snd_1585_);
lean_dec_ref(v_x_1582_);
v___x_1586_ = lean_apply_2(v_h__1_1583_, v_fst_1584_, v_snd_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_format_match__1_splitter(lean_object* v_00_u03b1_1587_, lean_object* v_motive_1588_, lean_object* v_x_1589_, lean_object* v_h__1_1590_){
_start:
{
lean_object* v_fst_1591_; lean_object* v_snd_1592_; lean_object* v___x_1593_; 
v_fst_1591_ = lean_ctor_get(v_x_1589_, 0);
lean_inc(v_fst_1591_);
v_snd_1592_ = lean_ctor_get(v_x_1589_, 1);
lean_inc(v_snd_1592_);
lean_dec_ref(v_x_1589_);
v___x_1593_ = lean_apply_2(v_h__1_1590_, v_fst_1591_, v_snd_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___lam__0(lean_object* v_keys_1594_, lean_object* v_v_1595_, lean_object* v_inst_1596_, lean_object* v_x_1597_){
_start:
{
if (lean_obj_tag(v_x_1597_) == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v_inst_1596_);
v___x_1598_ = lean_unsigned_to_nat(1u);
v___x_1599_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1599_, 0, v_keys_1594_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
lean_ctor_set(v___x_1599_, 2, v_v_1595_);
v___x_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
else
{
lean_object* v_val_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1610_; 
v_val_1601_ = lean_ctor_get(v_x_1597_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_x_1597_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1603_ = v_x_1597_;
v_isShared_1604_ = v_isSharedCheck_1610_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_val_1601_);
lean_dec(v_x_1597_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1610_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1596_, v_keys_1594_, v_v_1595_, v___x_1605_, v_val_1601_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1606_);
v___x_1608_ = v___x_1603_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3));
v___x_1616_ = lean_unsigned_to_nat(23u);
v___x_1617_ = lean_unsigned_to_nat(209u);
v___x_1618_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2));
v___x_1619_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0));
v___x_1620_ = l_mkPanicMessageWithDecl(v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg(lean_object* v_inst_1621_, lean_object* v_d_1622_, lean_object* v_keys_1623_, lean_object* v_v_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1625_ = lean_array_get_size(v_keys_1623_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_nat_dec_eq(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_k_1632_; uint64_t v___x_1633_; size_t v_h_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
lean_inc_ref(v_keys_1623_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1628_, 0, v_keys_1623_);
lean_closure_set(v___f_1628_, 1, v_v_1624_);
lean_closure_set(v___f_1628_, 2, v_inst_1621_);
v___x_1629_ = lean_box(0);
v___x_1630_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0));
v___x_1631_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1));
v_k_1632_ = lean_array_get(v___x_1629_, v_keys_1623_, v___x_1626_);
lean_dec_ref(v_keys_1623_);
v___x_1633_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1632_);
v_h_1634_ = lean_uint64_to_usize(v___x_1633_);
v___x_1635_ = ((size_t)1ULL);
v___x_1636_ = l_Lean_PersistentHashMap_alterAux___redArg(v___x_1630_, v___x_1631_, v___f_1628_, v_d_1622_, v_h_1634_, v___x_1635_, v_k_1632_);
return v___x_1636_;
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_v_1624_);
lean_dec_ref(v_keys_1623_);
lean_dec_ref(v_d_1622_);
lean_dec_ref(v_inst_1621_);
v___x_1637_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___closed__0, &l_Lean_Meta_DiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabited___closed__0);
v___x_1638_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4, &l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4);
v___x_1639_ = l_panic___redArg(v___x_1637_, v___x_1638_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue(lean_object* v_00_u03b1_1640_, lean_object* v_inst_1641_, lean_object* v_d_1642_, lean_object* v_keys_1643_, lean_object* v_v_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_1641_, v_d_1642_, v_keys_1643_, v_v_1644_);
return v___x_1645_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Array_instInhabited___redArg();
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg(lean_object* v_msg_1647_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0, &l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_panic_fn_borrowed(v___x_1649_, v_msg_1647_);
lean_dec_ref_known(v___x_1649_, 2);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0(lean_object* v_00_u03b1_1651_, lean_object* v_msg_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg(v_msg_1652_);
return v___x_1653_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__1));
v___x_1657_ = lean_unsigned_to_nat(15u);
v___x_1658_ = lean_unsigned_to_nat(238u);
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__0));
v___x_1660_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0));
v___x_1661_ = l_mkPanicMessageWithDecl(v___x_1660_, v___x_1659_, v___x_1658_, v___x_1657_, v___x_1656_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg(lean_object* v_x_1662_){
_start:
{
switch(lean_obj_tag(v_x_1662_))
{
case 0:
{
lean_object* v_key_1663_; lean_object* v_child_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_key_1663_ = lean_ctor_get(v_x_1662_, 0);
lean_inc(v_key_1663_);
v_child_1664_ = lean_ctor_get(v_x_1662_, 1);
lean_inc_ref(v_child_1664_);
lean_dec_ref_known(v_x_1662_, 2);
v___x_1665_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_key_1663_);
lean_ctor_set(v___x_1666_, 1, v_child_1664_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1667_);
v___x_1669_ = lean_array_push(v___x_1668_, v___x_1666_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1665_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
return v___x_1670_;
}
case 1:
{
lean_object* v_vs_1671_; lean_object* v_children_1672_; lean_object* v___x_1673_; 
v_vs_1671_ = lean_ctor_get(v_x_1662_, 0);
lean_inc_ref(v_vs_1671_);
v_children_1672_ = lean_ctor_get(v_x_1662_, 1);
lean_inc_ref(v_children_1672_);
lean_dec_ref_known(v_x_1662_, 2);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_vs_1671_);
lean_ctor_set(v___x_1673_, 1, v_children_1672_);
return v___x_1673_;
}
case 2:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref_known(v_x_1662_, 1);
v___x_1674_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2);
v___x_1675_ = l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg(v___x_1674_);
return v___x_1675_;
}
default: 
{
lean_object* v_keys_1676_; lean_object* v_i_1677_; lean_object* v_v_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1700_; 
v_keys_1676_ = lean_ctor_get(v_x_1662_, 0);
v_i_1677_ = lean_ctor_get(v_x_1662_, 1);
v_v_1678_ = lean_ctor_get(v_x_1662_, 2);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_x_1662_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1680_ = v_x_1662_;
v_isShared_1681_ = v_isSharedCheck_1700_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_v_1678_);
lean_inc(v_i_1677_);
lean_inc(v_keys_1676_);
lean_dec(v_x_1662_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1700_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = lean_array_get_size(v_keys_1676_);
v___x_1683_ = lean_nat_dec_lt(v_i_1677_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_del_object(v___x_1680_);
lean_dec(v_i_1677_);
lean_dec_ref(v_keys_1676_);
v___x_1684_ = lean_unsigned_to_nat(1u);
v___x_1685_ = lean_mk_empty_array_with_capacity(v___x_1684_);
v___x_1686_ = lean_array_push(v___x_1685_, v_v_1678_);
v___x_1687_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg___closed__0));
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1689_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
v___x_1690_ = lean_array_fget(v_keys_1676_, v_i_1677_);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_nat_add(v_i_1677_, v___x_1691_);
lean_dec(v_i_1677_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v___x_1692_);
v___x_1694_ = v___x_1680_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_keys_1676_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1678_);
v___x_1694_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1690_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_mk_empty_array_with_capacity(v___x_1691_);
v___x_1697_ = lean_array_push(v___x_1696_, v___x_1695_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1689_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
return v___x_1698_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold(lean_object* v_00_u03b1_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg(v_x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_match__1_splitter___redArg(lean_object* v_x_1704_, lean_object* v_h__1_1705_, lean_object* v_h__2_1706_, lean_object* v_h__3_1707_, lean_object* v_h__4_1708_){
_start:
{
switch(lean_obj_tag(v_x_1704_))
{
case 0:
{
lean_object* v_key_1709_; lean_object* v_child_1710_; lean_object* v___x_1711_; 
lean_dec(v_h__4_1708_);
lean_dec(v_h__3_1707_);
lean_dec(v_h__2_1706_);
v_key_1709_ = lean_ctor_get(v_x_1704_, 0);
lean_inc(v_key_1709_);
v_child_1710_ = lean_ctor_get(v_x_1704_, 1);
lean_inc_ref(v_child_1710_);
lean_dec_ref_known(v_x_1704_, 2);
v___x_1711_ = lean_apply_2(v_h__1_1705_, v_key_1709_, v_child_1710_);
return v___x_1711_;
}
case 1:
{
lean_object* v_vs_1712_; lean_object* v_children_1713_; lean_object* v___x_1714_; 
lean_dec(v_h__4_1708_);
lean_dec(v_h__3_1707_);
lean_dec(v_h__1_1705_);
v_vs_1712_ = lean_ctor_get(v_x_1704_, 0);
lean_inc_ref(v_vs_1712_);
v_children_1713_ = lean_ctor_get(v_x_1704_, 1);
lean_inc_ref(v_children_1713_);
lean_dec_ref_known(v_x_1704_, 2);
v___x_1714_ = lean_apply_2(v_h__2_1706_, v_vs_1712_, v_children_1713_);
return v___x_1714_;
}
case 2:
{
lean_object* v_t_1715_; lean_object* v___x_1716_; 
lean_dec(v_h__3_1707_);
lean_dec(v_h__2_1706_);
lean_dec(v_h__1_1705_);
v_t_1715_ = lean_ctor_get(v_x_1704_, 0);
lean_inc_ref(v_t_1715_);
lean_dec_ref_known(v_x_1704_, 1);
v___x_1716_ = lean_apply_1(v_h__4_1708_, v_t_1715_);
return v___x_1716_;
}
default: 
{
lean_object* v_keys_1717_; lean_object* v_i_1718_; lean_object* v_v_1719_; lean_object* v___x_1720_; 
lean_dec(v_h__4_1708_);
lean_dec(v_h__2_1706_);
lean_dec(v_h__1_1705_);
v_keys_1717_ = lean_ctor_get(v_x_1704_, 0);
lean_inc_ref(v_keys_1717_);
v_i_1718_ = lean_ctor_get(v_x_1704_, 1);
lean_inc(v_i_1718_);
v_v_1719_ = lean_ctor_get(v_x_1704_, 2);
lean_inc(v_v_1719_);
lean_dec_ref_known(v_x_1704_, 3);
v___x_1720_ = lean_apply_3(v_h__3_1707_, v_keys_1717_, v_i_1718_, v_v_1719_);
return v___x_1720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_match__1_splitter(lean_object* v_00_u03b1_1721_, lean_object* v_motive_1722_, lean_object* v_x_1723_, lean_object* v_h__1_1724_, lean_object* v_h__2_1725_, lean_object* v_h__3_1726_, lean_object* v_h__4_1727_){
_start:
{
switch(lean_obj_tag(v_x_1723_))
{
case 0:
{
lean_object* v_key_1728_; lean_object* v_child_1729_; lean_object* v___x_1730_; 
lean_dec(v_h__4_1727_);
lean_dec(v_h__3_1726_);
lean_dec(v_h__2_1725_);
v_key_1728_ = lean_ctor_get(v_x_1723_, 0);
lean_inc(v_key_1728_);
v_child_1729_ = lean_ctor_get(v_x_1723_, 1);
lean_inc_ref(v_child_1729_);
lean_dec_ref_known(v_x_1723_, 2);
v___x_1730_ = lean_apply_2(v_h__1_1724_, v_key_1728_, v_child_1729_);
return v___x_1730_;
}
case 1:
{
lean_object* v_vs_1731_; lean_object* v_children_1732_; lean_object* v___x_1733_; 
lean_dec(v_h__4_1727_);
lean_dec(v_h__3_1726_);
lean_dec(v_h__1_1724_);
v_vs_1731_ = lean_ctor_get(v_x_1723_, 0);
lean_inc_ref(v_vs_1731_);
v_children_1732_ = lean_ctor_get(v_x_1723_, 1);
lean_inc_ref(v_children_1732_);
lean_dec_ref_known(v_x_1723_, 2);
v___x_1733_ = lean_apply_2(v_h__2_1725_, v_vs_1731_, v_children_1732_);
return v___x_1733_;
}
case 2:
{
lean_object* v_t_1734_; lean_object* v___x_1735_; 
lean_dec(v_h__3_1726_);
lean_dec(v_h__2_1725_);
lean_dec(v_h__1_1724_);
v_t_1734_ = lean_ctor_get(v_x_1723_, 0);
lean_inc_ref(v_t_1734_);
lean_dec_ref_known(v_x_1723_, 1);
v___x_1735_ = lean_apply_1(v_h__4_1727_, v_t_1734_);
return v___x_1735_;
}
default: 
{
lean_object* v_keys_1736_; lean_object* v_i_1737_; lean_object* v_v_1738_; lean_object* v___x_1739_; 
lean_dec(v_h__4_1727_);
lean_dec(v_h__2_1725_);
lean_dec(v_h__1_1724_);
v_keys_1736_ = lean_ctor_get(v_x_1723_, 0);
lean_inc_ref(v_keys_1736_);
v_i_1737_ = lean_ctor_get(v_x_1723_, 1);
lean_inc(v_i_1737_);
v_v_1738_ = lean_ctor_get(v_x_1723_, 2);
lean_inc(v_v_1738_);
lean_dec_ref_known(v_x_1723_, 3);
v___x_1739_ = lean_apply_3(v_h__3_1726_, v_keys_1736_, v_i_1737_, v_v_1738_);
return v___x_1739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_match__1_splitter___redArg(lean_object* v_x_1740_, lean_object* v_h__1_1741_, lean_object* v_h__2_1742_, lean_object* v_h__3_1743_, lean_object* v_h__4_1744_){
_start:
{
switch(lean_obj_tag(v_x_1740_))
{
case 0:
{
lean_object* v_key_1745_; lean_object* v_child_1746_; lean_object* v___x_1747_; 
lean_dec(v_h__4_1744_);
lean_dec(v_h__3_1743_);
lean_dec(v_h__2_1742_);
v_key_1745_ = lean_ctor_get(v_x_1740_, 0);
lean_inc(v_key_1745_);
v_child_1746_ = lean_ctor_get(v_x_1740_, 1);
lean_inc_ref(v_child_1746_);
lean_dec_ref_known(v_x_1740_, 2);
v___x_1747_ = lean_apply_2(v_h__1_1741_, v_key_1745_, v_child_1746_);
return v___x_1747_;
}
case 1:
{
lean_object* v_vs_1748_; lean_object* v_children_1749_; lean_object* v_toList_1750_; lean_object* v___x_1751_; 
lean_dec(v_h__4_1744_);
lean_dec(v_h__3_1743_);
lean_dec(v_h__1_1741_);
v_vs_1748_ = lean_ctor_get(v_x_1740_, 0);
lean_inc_ref(v_vs_1748_);
v_children_1749_ = lean_ctor_get(v_x_1740_, 1);
lean_inc_ref(v_children_1749_);
lean_dec_ref_known(v_x_1740_, 2);
v_toList_1750_ = lean_array_to_list(v_children_1749_);
v___x_1751_ = lean_apply_2(v_h__2_1742_, v_vs_1748_, v_toList_1750_);
return v___x_1751_;
}
case 2:
{
lean_object* v_t_1752_; lean_object* v___x_1753_; 
lean_dec(v_h__4_1744_);
lean_dec(v_h__2_1742_);
lean_dec(v_h__1_1741_);
v_t_1752_ = lean_ctor_get(v_x_1740_, 0);
lean_inc_ref(v_t_1752_);
lean_dec_ref_known(v_x_1740_, 1);
v___x_1753_ = lean_apply_1(v_h__3_1743_, v_t_1752_);
return v___x_1753_;
}
default: 
{
lean_object* v_keys_1754_; lean_object* v_i_1755_; lean_object* v_v_1756_; lean_object* v___x_1757_; 
lean_dec(v_h__3_1743_);
lean_dec(v_h__2_1742_);
lean_dec(v_h__1_1741_);
v_keys_1754_ = lean_ctor_get(v_x_1740_, 0);
lean_inc_ref(v_keys_1754_);
v_i_1755_ = lean_ctor_get(v_x_1740_, 1);
lean_inc(v_i_1755_);
v_v_1756_ = lean_ctor_get(v_x_1740_, 2);
lean_inc(v_v_1756_);
lean_dec_ref_known(v_x_1740_, 3);
v___x_1757_ = lean_apply_3(v_h__4_1744_, v_keys_1754_, v_i_1755_, v_v_1756_);
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_match__1_splitter(lean_object* v_00_u03b1_1758_, lean_object* v_motive_1759_, lean_object* v_x_1760_, lean_object* v_h__1_1761_, lean_object* v_h__2_1762_, lean_object* v_h__3_1763_, lean_object* v_h__4_1764_){
_start:
{
switch(lean_obj_tag(v_x_1760_))
{
case 0:
{
lean_object* v_key_1765_; lean_object* v_child_1766_; lean_object* v___x_1767_; 
lean_dec(v_h__4_1764_);
lean_dec(v_h__3_1763_);
lean_dec(v_h__2_1762_);
v_key_1765_ = lean_ctor_get(v_x_1760_, 0);
lean_inc(v_key_1765_);
v_child_1766_ = lean_ctor_get(v_x_1760_, 1);
lean_inc_ref(v_child_1766_);
lean_dec_ref_known(v_x_1760_, 2);
v___x_1767_ = lean_apply_2(v_h__1_1761_, v_key_1765_, v_child_1766_);
return v___x_1767_;
}
case 1:
{
lean_object* v_vs_1768_; lean_object* v_children_1769_; lean_object* v_toList_1770_; lean_object* v___x_1771_; 
lean_dec(v_h__4_1764_);
lean_dec(v_h__3_1763_);
lean_dec(v_h__1_1761_);
v_vs_1768_ = lean_ctor_get(v_x_1760_, 0);
lean_inc_ref(v_vs_1768_);
v_children_1769_ = lean_ctor_get(v_x_1760_, 1);
lean_inc_ref(v_children_1769_);
lean_dec_ref_known(v_x_1760_, 2);
v_toList_1770_ = lean_array_to_list(v_children_1769_);
v___x_1771_ = lean_apply_2(v_h__2_1762_, v_vs_1768_, v_toList_1770_);
return v___x_1771_;
}
case 2:
{
lean_object* v_t_1772_; lean_object* v___x_1773_; 
lean_dec(v_h__4_1764_);
lean_dec(v_h__2_1762_);
lean_dec(v_h__1_1761_);
v_t_1772_ = lean_ctor_get(v_x_1760_, 0);
lean_inc_ref(v_t_1772_);
lean_dec_ref_known(v_x_1760_, 1);
v___x_1773_ = lean_apply_1(v_h__3_1763_, v_t_1772_);
return v___x_1773_;
}
default: 
{
lean_object* v_keys_1774_; lean_object* v_i_1775_; lean_object* v_v_1776_; lean_object* v___x_1777_; 
lean_dec(v_h__3_1763_);
lean_dec(v_h__2_1762_);
lean_dec(v_h__1_1761_);
v_keys_1774_ = lean_ctor_get(v_x_1760_, 0);
lean_inc_ref(v_keys_1774_);
v_i_1775_ = lean_ctor_get(v_x_1760_, 1);
lean_inc(v_i_1775_);
v_v_1776_ = lean_ctor_get(v_x_1760_, 2);
lean_inc(v_v_1776_);
lean_dec_ref_known(v_x_1760_, 3);
v___x_1777_ = lean_apply_3(v_h__4_1764_, v_keys_1774_, v_i_1775_, v_v_1776_);
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_weights_match__1_splitter___redArg(lean_object* v_x_1778_, lean_object* v_h__1_1779_, lean_object* v_h__2_1780_){
_start:
{
if (lean_obj_tag(v_x_1778_) == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v_h__2_1780_);
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_apply_1(v_h__1_1779_, v___x_1781_);
return v___x_1782_;
}
else
{
lean_object* v_head_1783_; lean_object* v_tail_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; lean_object* v___x_1787_; 
lean_dec(v_h__1_1779_);
v_head_1783_ = lean_ctor_get(v_x_1778_, 0);
lean_inc(v_head_1783_);
v_tail_1784_ = lean_ctor_get(v_x_1778_, 1);
lean_inc(v_tail_1784_);
lean_dec_ref_known(v_x_1778_, 2);
v_fst_1785_ = lean_ctor_get(v_head_1783_, 0);
lean_inc(v_fst_1785_);
v_snd_1786_ = lean_ctor_get(v_head_1783_, 1);
lean_inc(v_snd_1786_);
lean_dec(v_head_1783_);
v___x_1787_ = lean_apply_3(v_h__2_1780_, v_fst_1785_, v_snd_1786_, v_tail_1784_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_weights_match__1_splitter(lean_object* v_00_u03b1_1788_, lean_object* v_motive_1789_, lean_object* v_x_1790_, lean_object* v_h__1_1791_, lean_object* v_h__2_1792_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec(v_h__2_1792_);
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_apply_1(v_h__1_1791_, v___x_1793_);
return v___x_1794_;
}
else
{
lean_object* v_head_1795_; lean_object* v_tail_1796_; lean_object* v_fst_1797_; lean_object* v_snd_1798_; lean_object* v___x_1799_; 
lean_dec(v_h__1_1791_);
v_head_1795_ = lean_ctor_get(v_x_1790_, 0);
lean_inc(v_head_1795_);
v_tail_1796_ = lean_ctor_get(v_x_1790_, 1);
lean_inc(v_tail_1796_);
lean_dec_ref_known(v_x_1790_, 2);
v_fst_1797_ = lean_ctor_get(v_head_1795_, 0);
lean_inc(v_fst_1797_);
v_snd_1798_ = lean_ctor_get(v_head_1795_, 1);
lean_inc(v_snd_1798_);
lean_dec(v_head_1795_);
v___x_1799_ = lean_apply_3(v_h__2_1792_, v_fst_1797_, v_snd_1798_, v_tail_1796_);
return v___x_1799_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(lean_object* v_x1_1800_, lean_object* v_x2_1801_){
_start:
{
lean_object* v_snd_1802_; lean_object* v_snd_1803_; lean_object* v_snd_1804_; lean_object* v_snd_1805_; uint8_t v___x_1806_; 
v_snd_1802_ = lean_ctor_get(v_x1_1800_, 1);
v_snd_1803_ = lean_ctor_get(v_x2_1801_, 1);
v_snd_1804_ = lean_ctor_get(v_snd_1802_, 1);
v_snd_1805_ = lean_ctor_get(v_snd_1803_, 1);
v___x_1806_ = lean_nat_dec_lt(v_snd_1804_, v_snd_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0___boxed(lean_object* v_x1_1807_, lean_object* v_x2_1808_){
_start:
{
uint8_t v_res_1809_; lean_object* v_r_1810_; 
v_res_1809_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(v_x1_1807_, v_x2_1808_);
lean_dec_ref(v_x2_1808_);
lean_dec_ref(v_x1_1807_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(lean_object* v_hi_1811_, lean_object* v_pivot_1812_, lean_object* v_as_1813_, lean_object* v_i_1814_, lean_object* v_k_1815_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_nat_dec_lt(v_k_1815_, v_hi_1811_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v_k_1815_);
v___x_1817_ = lean_array_fswap(v_as_1813_, v_i_1814_, v_hi_1811_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_i_1814_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v_snd_1820_; lean_object* v_snd_1821_; lean_object* v_snd_1822_; lean_object* v_snd_1823_; uint8_t v___x_1824_; 
v___x_1819_ = lean_array_fget_borrowed(v_as_1813_, v_k_1815_);
v_snd_1820_ = lean_ctor_get(v___x_1819_, 1);
v_snd_1821_ = lean_ctor_get(v_pivot_1812_, 1);
v_snd_1822_ = lean_ctor_get(v_snd_1820_, 1);
v_snd_1823_ = lean_ctor_get(v_snd_1821_, 1);
v___x_1824_ = lean_nat_dec_lt(v_snd_1822_, v_snd_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_nat_add(v_k_1815_, v___x_1825_);
lean_dec(v_k_1815_);
v_k_1815_ = v___x_1826_;
goto _start;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1828_ = lean_array_fswap(v_as_1813_, v_i_1814_, v_k_1815_);
v___x_1829_ = lean_unsigned_to_nat(1u);
v___x_1830_ = lean_nat_add(v_i_1814_, v___x_1829_);
lean_dec(v_i_1814_);
v___x_1831_ = lean_nat_add(v_k_1815_, v___x_1829_);
lean_dec(v_k_1815_);
v_as_1813_ = v___x_1828_;
v_i_1814_ = v___x_1830_;
v_k_1815_ = v___x_1831_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg___boxed(lean_object* v_hi_1833_, lean_object* v_pivot_1834_, lean_object* v_as_1835_, lean_object* v_i_1836_, lean_object* v_k_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(v_hi_1833_, v_pivot_1834_, v_as_1835_, v_i_1836_, v_k_1837_);
lean_dec_ref(v_pivot_1834_);
lean_dec(v_hi_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(lean_object* v_n_1839_, lean_object* v_as_1840_, lean_object* v_lo_1841_, lean_object* v_hi_1842_){
_start:
{
lean_object* v___y_1844_; uint8_t v___x_1854_; 
v___x_1854_ = lean_nat_dec_lt(v_lo_1841_, v_hi_1842_);
if (v___x_1854_ == 0)
{
lean_dec(v_lo_1841_);
return v_as_1840_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v_mid_1857_; lean_object* v___y_1859_; lean_object* v___y_1865_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1855_ = lean_nat_add(v_lo_1841_, v_hi_1842_);
v___x_1856_ = lean_unsigned_to_nat(1u);
v_mid_1857_ = lean_nat_shiftr(v___x_1855_, v___x_1856_);
lean_dec(v___x_1855_);
v___x_1870_ = lean_array_fget_borrowed(v_as_1840_, v_mid_1857_);
v___x_1871_ = lean_array_fget_borrowed(v_as_1840_, v_lo_1841_);
v___x_1872_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(v___x_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
v___y_1865_ = v_as_1840_;
goto v___jp_1864_;
}
else
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_array_fswap(v_as_1840_, v_lo_1841_, v_mid_1857_);
v___y_1865_ = v___x_1873_;
goto v___jp_1864_;
}
v___jp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = lean_array_fget_borrowed(v___y_1859_, v_mid_1857_);
v___x_1861_ = lean_array_fget_borrowed(v___y_1859_, v_hi_1842_);
v___x_1862_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec(v_mid_1857_);
v___y_1844_ = v___y_1859_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_array_fswap(v___y_1859_, v_mid_1857_, v_hi_1842_);
lean_dec(v_mid_1857_);
v___y_1844_ = v___x_1863_;
goto v___jp_1843_;
}
}
v___jp_1864_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1866_ = lean_array_fget_borrowed(v___y_1865_, v_hi_1842_);
v___x_1867_ = lean_array_fget_borrowed(v___y_1865_, v_lo_1841_);
v___x_1868_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(v___x_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
v___y_1859_ = v___y_1865_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_array_fswap(v___y_1865_, v_lo_1841_, v_hi_1842_);
v___y_1859_ = v___x_1869_;
goto v___jp_1858_;
}
}
}
v___jp_1843_:
{
lean_object* v_pivot_1845_; lean_object* v___x_1846_; lean_object* v_fst_1847_; lean_object* v_snd_1848_; uint8_t v___x_1849_; 
v_pivot_1845_ = lean_array_fget(v___y_1844_, v_hi_1842_);
lean_inc_n(v_lo_1841_, 2);
v___x_1846_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(v_hi_1842_, v_pivot_1845_, v___y_1844_, v_lo_1841_, v_lo_1841_);
lean_dec(v_pivot_1845_);
v_fst_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_fst_1847_);
v_snd_1848_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_snd_1848_);
lean_dec_ref(v___x_1846_);
v___x_1849_ = lean_nat_dec_le(v_hi_1842_, v_fst_1847_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(v_n_1839_, v_snd_1848_, v_lo_1841_, v_fst_1847_);
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = lean_nat_add(v_fst_1847_, v___x_1851_);
lean_dec(v_fst_1847_);
v_as_1840_ = v___x_1850_;
v_lo_1841_ = v___x_1852_;
goto _start;
}
else
{
lean_dec(v_fst_1847_);
lean_dec(v_lo_1841_);
return v_snd_1848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___boxed(lean_object* v_n_1874_, lean_object* v_as_1875_, lean_object* v_lo_1876_, lean_object* v_hi_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(v_n_1874_, v_as_1875_, v_lo_1876_, v_hi_1877_);
lean_dec(v_hi_1877_);
lean_dec(v_n_1874_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(lean_object* v_a_1879_, lean_object* v_b_1880_, lean_object* v_x_1881_){
_start:
{
if (lean_obj_tag(v_x_1881_) == 0)
{
lean_dec(v_b_1880_);
lean_dec(v_a_1879_);
return v_x_1881_;
}
else
{
lean_object* v_key_1882_; lean_object* v_value_1883_; lean_object* v_tail_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1896_; 
v_key_1882_ = lean_ctor_get(v_x_1881_, 0);
v_value_1883_ = lean_ctor_get(v_x_1881_, 1);
v_tail_1884_ = lean_ctor_get(v_x_1881_, 2);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_x_1881_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1886_ = v_x_1881_;
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_tail_1884_);
lean_inc(v_value_1883_);
lean_inc(v_key_1882_);
lean_dec(v_x_1881_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
uint8_t v___x_1888_; 
v___x_1888_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1882_, v_a_1879_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(v_a_1879_, v_b_1880_, v_tail_1884_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 2, v___x_1889_);
v___x_1891_ = v___x_1886_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_key_1882_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_value_1883_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
else
{
lean_object* v___x_1894_; 
lean_dec(v_value_1883_);
lean_dec(v_key_1882_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v_b_1880_);
lean_ctor_set(v___x_1886_, 0, v_a_1879_);
v___x_1894_ = v___x_1886_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1879_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_b_1880_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_tail_1884_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9___redArg(lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
if (lean_obj_tag(v_x_1898_) == 0)
{
return v_x_1897_;
}
else
{
lean_object* v_key_1899_; lean_object* v_value_1900_; lean_object* v_tail_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1924_; 
v_key_1899_ = lean_ctor_get(v_x_1898_, 0);
v_value_1900_ = lean_ctor_get(v_x_1898_, 1);
v_tail_1901_ = lean_ctor_get(v_x_1898_, 2);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_x_1898_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1903_ = v_x_1898_;
v_isShared_1904_ = v_isSharedCheck_1924_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_tail_1901_);
lean_inc(v_value_1900_);
lean_inc(v_key_1899_);
lean_dec(v_x_1898_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1924_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; uint64_t v___x_1906_; uint64_t v___x_1907_; uint64_t v___x_1908_; uint64_t v_fold_1909_; uint64_t v___x_1910_; uint64_t v___x_1911_; uint64_t v___x_1912_; size_t v___x_1913_; size_t v___x_1914_; size_t v___x_1915_; size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1905_ = lean_array_get_size(v_x_1897_);
v___x_1906_ = l_Lean_Meta_DiscrTree_Key_hash(v_key_1899_);
v___x_1907_ = 32ULL;
v___x_1908_ = lean_uint64_shift_right(v___x_1906_, v___x_1907_);
v_fold_1909_ = lean_uint64_xor(v___x_1906_, v___x_1908_);
v___x_1910_ = 16ULL;
v___x_1911_ = lean_uint64_shift_right(v_fold_1909_, v___x_1910_);
v___x_1912_ = lean_uint64_xor(v_fold_1909_, v___x_1911_);
v___x_1913_ = lean_uint64_to_usize(v___x_1912_);
v___x_1914_ = lean_usize_of_nat(v___x_1905_);
v___x_1915_ = ((size_t)1ULL);
v___x_1916_ = lean_usize_sub(v___x_1914_, v___x_1915_);
v___x_1917_ = lean_usize_land(v___x_1913_, v___x_1916_);
v___x_1918_ = lean_array_uget_borrowed(v_x_1897_, v___x_1917_);
lean_inc(v___x_1918_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 2, v___x_1918_);
v___x_1920_ = v___x_1903_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_key_1899_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_value_1900_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_array_uset(v_x_1897_, v___x_1917_, v___x_1920_);
v_x_1897_ = v___x_1921_;
v_x_1898_ = v_tail_1901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5___redArg(lean_object* v_i_1925_, lean_object* v_source_1926_, lean_object* v_target_1927_){
_start:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = lean_array_get_size(v_source_1926_);
v___x_1929_ = lean_nat_dec_lt(v_i_1925_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_dec_ref(v_source_1926_);
lean_dec(v_i_1925_);
return v_target_1927_;
}
else
{
lean_object* v_es_1930_; lean_object* v___x_1931_; lean_object* v_source_1932_; lean_object* v_target_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_es_1930_ = lean_array_fget(v_source_1926_, v_i_1925_);
v___x_1931_ = lean_box(0);
v_source_1932_ = lean_array_fset(v_source_1926_, v_i_1925_, v___x_1931_);
v_target_1933_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9___redArg(v_target_1927_, v_es_1930_);
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_nat_add(v_i_1925_, v___x_1934_);
lean_dec(v_i_1925_);
v_i_1925_ = v___x_1935_;
v_source_1926_ = v_source_1932_;
v_target_1927_ = v_target_1933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4___redArg(lean_object* v_data_1937_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v_nbuckets_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1938_ = lean_array_get_size(v_data_1937_);
v___x_1939_ = lean_unsigned_to_nat(2u);
v_nbuckets_1940_ = lean_nat_mul(v___x_1938_, v___x_1939_);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_mk_array(v_nbuckets_1940_, v___x_1942_);
v___x_1944_ = lean_array_propagate_mark(v_data_1937_, v___x_1943_);
v___x_1945_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5___redArg(v___x_1941_, v_data_1937_, v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(lean_object* v_a_1946_, lean_object* v_x_1947_){
_start:
{
if (lean_obj_tag(v_x_1947_) == 0)
{
uint8_t v___x_1948_; 
v___x_1948_ = 0;
return v___x_1948_;
}
else
{
lean_object* v_key_1949_; lean_object* v_tail_1950_; uint8_t v___x_1951_; 
v_key_1949_ = lean_ctor_get(v_x_1947_, 0);
v_tail_1950_ = lean_ctor_get(v_x_1947_, 2);
v___x_1951_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1949_, v_a_1946_);
if (v___x_1951_ == 0)
{
v_x_1947_ = v_tail_1950_;
goto _start;
}
else
{
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg___boxed(lean_object* v_a_1953_, lean_object* v_x_1954_){
_start:
{
uint8_t v_res_1955_; lean_object* v_r_1956_; 
v_res_1955_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(v_a_1953_, v_x_1954_);
lean_dec(v_x_1954_);
lean_dec(v_a_1953_);
v_r_1956_ = lean_box(v_res_1955_);
return v_r_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2___redArg(lean_object* v_m_1957_, lean_object* v_a_1958_, lean_object* v_b_1959_){
_start:
{
lean_object* v_size_1960_; lean_object* v_buckets_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2004_; 
v_size_1960_ = lean_ctor_get(v_m_1957_, 0);
v_buckets_1961_ = lean_ctor_get(v_m_1957_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_m_1957_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1963_ = v_m_1957_;
v_isShared_1964_ = v_isSharedCheck_2004_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_buckets_1961_);
lean_inc(v_size_1960_);
lean_dec(v_m_1957_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2004_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; uint64_t v___x_1966_; uint64_t v___x_1967_; uint64_t v___x_1968_; uint64_t v_fold_1969_; uint64_t v___x_1970_; uint64_t v___x_1971_; uint64_t v___x_1972_; size_t v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; size_t v___x_1977_; lean_object* v_bkt_1978_; uint8_t v___x_1979_; 
v___x_1965_ = lean_array_get_size(v_buckets_1961_);
v___x_1966_ = l_Lean_Meta_DiscrTree_Key_hash(v_a_1958_);
v___x_1967_ = 32ULL;
v___x_1968_ = lean_uint64_shift_right(v___x_1966_, v___x_1967_);
v_fold_1969_ = lean_uint64_xor(v___x_1966_, v___x_1968_);
v___x_1970_ = 16ULL;
v___x_1971_ = lean_uint64_shift_right(v_fold_1969_, v___x_1970_);
v___x_1972_ = lean_uint64_xor(v_fold_1969_, v___x_1971_);
v___x_1973_ = lean_uint64_to_usize(v___x_1972_);
v___x_1974_ = lean_usize_of_nat(v___x_1965_);
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_sub(v___x_1974_, v___x_1975_);
v___x_1977_ = lean_usize_land(v___x_1973_, v___x_1976_);
v_bkt_1978_ = lean_array_uget_borrowed(v_buckets_1961_, v___x_1977_);
v___x_1979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(v_a_1958_, v_bkt_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v_size_x27_1981_; lean_object* v___x_1982_; lean_object* v_buckets_x27_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1980_ = lean_unsigned_to_nat(1u);
v_size_x27_1981_ = lean_nat_add(v_size_1960_, v___x_1980_);
lean_dec(v_size_1960_);
lean_inc(v_bkt_1978_);
v___x_1982_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1982_, 0, v_a_1958_);
lean_ctor_set(v___x_1982_, 1, v_b_1959_);
lean_ctor_set(v___x_1982_, 2, v_bkt_1978_);
v_buckets_x27_1983_ = lean_array_uset(v_buckets_1961_, v___x_1977_, v___x_1982_);
v___x_1984_ = lean_unsigned_to_nat(4u);
v___x_1985_ = lean_nat_mul(v_size_x27_1981_, v___x_1984_);
v___x_1986_ = lean_unsigned_to_nat(3u);
v___x_1987_ = lean_nat_div(v___x_1985_, v___x_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_array_get_size(v_buckets_x27_1983_);
v___x_1989_ = lean_nat_dec_le(v___x_1987_, v___x_1988_);
lean_dec(v___x_1987_);
if (v___x_1989_ == 0)
{
lean_object* v_val_1990_; lean_object* v___x_1992_; 
v_val_1990_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4___redArg(v_buckets_x27_1983_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v_val_1990_);
lean_ctor_set(v___x_1963_, 0, v_size_x27_1981_);
v___x_1992_ = v___x_1963_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_size_x27_1981_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_val_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v___x_1995_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v_buckets_x27_1983_);
lean_ctor_set(v___x_1963_, 0, v_size_x27_1981_);
v___x_1995_ = v___x_1963_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_size_x27_1981_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_buckets_x27_1983_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
lean_object* v___x_1997_; lean_object* v_buckets_x27_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
lean_inc(v_bkt_1978_);
v___x_1997_ = lean_box(0);
v_buckets_x27_1998_ = lean_array_uset(v_buckets_1961_, v___x_1977_, v___x_1997_);
v___x_1999_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(v_a_1958_, v_b_1959_, v_bkt_1978_);
v___x_2000_ = lean_array_uset(v_buckets_x27_1998_, v___x_1977_, v___x_1999_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___x_2000_);
v___x_2002_ = v___x_1963_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_size_1960_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(lean_object* v_a_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_box(0);
return v___x_2007_;
}
else
{
lean_object* v_key_2008_; lean_object* v_value_2009_; lean_object* v_tail_2010_; uint8_t v___x_2011_; 
v_key_2008_ = lean_ctor_get(v_x_2006_, 0);
v_value_2009_ = lean_ctor_get(v_x_2006_, 1);
v_tail_2010_ = lean_ctor_get(v_x_2006_, 2);
v___x_2011_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2008_, v_a_2005_);
if (v___x_2011_ == 0)
{
v_x_2006_ = v_tail_2010_;
goto _start;
}
else
{
lean_object* v___x_2013_; 
lean_inc(v_value_2009_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_value_2009_);
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg___boxed(lean_object* v_a_2014_, lean_object* v_x_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(v_a_2014_, v_x_2015_);
lean_dec(v_x_2015_);
lean_dec(v_a_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(lean_object* v_m_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_buckets_2019_; lean_object* v___x_2020_; uint64_t v___x_2021_; uint64_t v___x_2022_; uint64_t v___x_2023_; uint64_t v_fold_2024_; uint64_t v___x_2025_; uint64_t v___x_2026_; uint64_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; size_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_buckets_2019_ = lean_ctor_get(v_m_2017_, 1);
v___x_2020_ = lean_array_get_size(v_buckets_2019_);
v___x_2021_ = l_Lean_Meta_DiscrTree_Key_hash(v_a_2018_);
v___x_2022_ = 32ULL;
v___x_2023_ = lean_uint64_shift_right(v___x_2021_, v___x_2022_);
v_fold_2024_ = lean_uint64_xor(v___x_2021_, v___x_2023_);
v___x_2025_ = 16ULL;
v___x_2026_ = lean_uint64_shift_right(v_fold_2024_, v___x_2025_);
v___x_2027_ = lean_uint64_xor(v_fold_2024_, v___x_2026_);
v___x_2028_ = lean_uint64_to_usize(v___x_2027_);
v___x_2029_ = lean_usize_of_nat(v___x_2020_);
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_sub(v___x_2029_, v___x_2030_);
v___x_2032_ = lean_usize_land(v___x_2028_, v___x_2031_);
v___x_2033_ = lean_array_uget_borrowed(v_buckets_2019_, v___x_2032_);
v___x_2034_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(v_a_2018_, v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg___boxed(lean_object* v_m_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(v_m_2035_, v_a_2036_);
lean_dec(v_a_2036_);
lean_dec_ref(v_m_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(lean_object* v_as_2038_, size_t v_sz_2039_, size_t v_i_2040_, lean_object* v_b_2041_){
_start:
{
uint8_t v___x_2042_; 
v___x_2042_ = lean_usize_dec_lt(v_i_2040_, v_sz_2039_);
if (v___x_2042_ == 0)
{
return v_b_2041_;
}
else
{
lean_object* v_snd_2043_; lean_object* v_fst_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2112_; 
v_snd_2043_ = lean_ctor_get(v_b_2041_, 1);
v_fst_2044_ = lean_ctor_get(v_b_2041_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_b_2041_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2046_ = v_b_2041_;
v_isShared_2047_ = v_isSharedCheck_2112_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_snd_2043_);
lean_inc(v_fst_2044_);
lean_dec(v_b_2041_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2112_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2111_; 
v_fst_2048_ = lean_ctor_get(v_snd_2043_, 0);
v_snd_2049_ = lean_ctor_get(v_snd_2043_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_snd_2043_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2051_ = v_snd_2043_;
v_isShared_2052_ = v_isSharedCheck_2111_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_snd_2049_);
lean_inc(v_fst_2048_);
lean_dec(v_snd_2043_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2111_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_idx_2054_; lean_object* v_groups_2055_; lean_object* v_a_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2110_; 
v_a_2067_ = lean_array_uget(v_as_2038_, v_i_2040_);
v_fst_2068_ = lean_ctor_get(v_a_2067_, 0);
v_snd_2069_ = lean_ctor_get(v_a_2067_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2071_ = v_a_2067_;
v_isShared_2072_ = v_isSharedCheck_2110_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2069_);
lean_inc(v_fst_2068_);
lean_dec(v_a_2067_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2110_;
goto v_resetjp_2070_;
}
v___jp_2053_:
{
lean_object* v___x_2056_; lean_object* v_pos_2057_; lean_object* v___x_2059_; 
v___x_2056_ = lean_unsigned_to_nat(1u);
v_pos_2057_ = lean_nat_add(v_snd_2049_, v___x_2056_);
lean_dec(v_snd_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v_pos_2057_);
lean_ctor_set(v___x_2051_, 0, v_groups_2055_);
v___x_2059_ = v___x_2051_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_groups_2055_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_pos_2057_);
v___x_2059_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v___x_2059_);
lean_ctor_set(v___x_2046_, 0, v_idx_2054_);
v___x_2061_ = v___x_2046_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_idx_2054_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
size_t v___x_2062_; size_t v___x_2063_; 
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = lean_usize_add(v_i_2040_, v___x_2062_);
v_i_2040_ = v___x_2063_;
v_b_2041_ = v___x_2061_;
goto _start;
}
}
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(v_fst_2044_, v_fst_2068_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v___x_2074_; lean_object* v_idx_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2074_ = lean_array_get_size(v_fst_2048_);
lean_inc(v_fst_2068_);
v_idx_2075_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2___redArg(v_fst_2044_, v_fst_2068_, v___x_2074_);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_mk_empty_array_with_capacity(v___x_2076_);
v___x_2078_ = lean_array_push(v___x_2077_, v_snd_2069_);
lean_inc(v_snd_2049_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v_snd_2049_);
lean_ctor_set(v___x_2071_, 0, v___x_2078_);
v___x_2080_ = v___x_2071_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_snd_2049_);
v___x_2080_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v_groups_2082_; 
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v_fst_2068_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v_groups_2082_ = lean_array_push(v_fst_2048_, v___x_2081_);
v_idx_2054_ = v_idx_2075_;
v_groups_2055_ = v_groups_2082_;
goto v___jp_2053_;
}
}
else
{
lean_object* v_val_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
lean_del_object(v___x_2071_);
lean_dec(v_fst_2068_);
v_val_2084_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2085_ = lean_array_get_size(v_fst_2048_);
v___x_2086_ = lean_nat_dec_lt(v_val_2084_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_dec(v_val_2084_);
lean_dec(v_snd_2069_);
v_idx_2054_ = v_fst_2044_;
v_groups_2055_ = v_fst_2048_;
goto v___jp_2053_;
}
else
{
lean_object* v_v_2087_; lean_object* v_snd_2088_; lean_object* v_fst_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2109_; 
v_v_2087_ = lean_array_fget(v_fst_2048_, v_val_2084_);
v_snd_2088_ = lean_ctor_get(v_v_2087_, 1);
v_fst_2089_ = lean_ctor_get(v_v_2087_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_v_2087_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2091_ = v_v_2087_;
v_isShared_2092_ = v_isSharedCheck_2109_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_snd_2088_);
lean_inc(v_fst_2089_);
lean_dec(v_v_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2109_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_fst_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2107_; 
v_fst_2093_ = lean_ctor_get(v_snd_2088_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_snd_2088_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v_snd_2088_, 1);
lean_dec(v_unused_2108_);
v___x_2095_ = v_snd_2088_;
v_isShared_2096_ = v_isSharedCheck_2107_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_fst_2093_);
lean_dec(v_snd_2088_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2107_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v_xs_x27_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2097_ = lean_box(0);
v_xs_x27_2098_ = lean_array_fset(v_fst_2048_, v_val_2084_, v___x_2097_);
v___x_2099_ = lean_array_push(v_fst_2093_, v_snd_2069_);
lean_inc(v_snd_2049_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 1, v_snd_2049_);
lean_ctor_set(v___x_2095_, 0, v___x_2099_);
v___x_2101_ = v___x_2095_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_snd_2049_);
v___x_2101_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___x_2101_);
v___x_2103_ = v___x_2091_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_fst_2089_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_array_fset(v_xs_x27_2098_, v_val_2084_, v___x_2103_);
lean_dec(v_val_2084_);
v_idx_2054_ = v_fst_2044_;
v_groups_2055_ = v___x_2104_;
goto v___jp_2053_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg___boxed(lean_object* v_as_2113_, lean_object* v_sz_2114_, lean_object* v_i_2115_, lean_object* v_b_2116_){
_start:
{
size_t v_sz_boxed_2117_; size_t v_i_boxed_2118_; lean_object* v_res_2119_; 
v_sz_boxed_2117_ = lean_unbox_usize(v_sz_2114_);
lean_dec(v_sz_2114_);
v_i_boxed_2118_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(v_as_2113_, v_sz_boxed_2117_, v_i_boxed_2118_, v_b_2116_);
lean_dec_ref(v_as_2113_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(lean_object* v_as_2120_, size_t v_sz_2121_, size_t v_i_2122_, lean_object* v_b_2123_){
_start:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_usize_dec_lt(v_i_2122_, v_sz_2121_);
if (v___x_2124_ == 0)
{
return v_b_2123_;
}
else
{
lean_object* v_snd_2125_; lean_object* v_fst_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2167_; 
v_snd_2125_ = lean_ctor_get(v_b_2123_, 1);
v_fst_2126_ = lean_ctor_get(v_b_2123_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_b_2123_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2128_ = v_b_2123_;
v_isShared_2129_ = v_isSharedCheck_2167_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snd_2125_);
lean_inc(v_fst_2126_);
lean_dec(v_b_2123_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2167_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_fst_2130_; lean_object* v_snd_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2166_; 
v_fst_2130_ = lean_ctor_get(v_snd_2125_, 0);
v_snd_2131_ = lean_ctor_get(v_snd_2125_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_snd_2125_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2133_ = v_snd_2125_;
v_isShared_2134_ = v_isSharedCheck_2166_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_snd_2131_);
lean_inc(v_fst_2130_);
lean_dec(v_snd_2125_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2166_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_a_2135_; lean_object* v___x_2137_; 
v_a_2135_ = lean_array_uget_borrowed(v_as_2120_, v_i_2122_);
if (v_isShared_2134_ == 0)
{
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_fst_2130_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_snd_2131_);
v___x_2137_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v___x_2137_);
v___x_2139_ = v___x_2128_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_fst_2126_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
size_t v_sz_2140_; size_t v___x_2141_; lean_object* v___x_2142_; lean_object* v_snd_2143_; lean_object* v_fst_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2163_; 
v_sz_2140_ = lean_array_size(v_a_2135_);
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(v_a_2135_, v_sz_2140_, v___x_2141_, v___x_2139_);
v_snd_2143_ = lean_ctor_get(v___x_2142_, 1);
v_fst_2144_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2146_ = v___x_2142_;
v_isShared_2147_ = v_isSharedCheck_2163_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_snd_2143_);
lean_inc(v_fst_2144_);
lean_dec(v___x_2142_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2163_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_fst_2148_; lean_object* v_snd_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2162_; 
v_fst_2148_ = lean_ctor_get(v_snd_2143_, 0);
v_snd_2149_ = lean_ctor_get(v_snd_2143_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_snd_2143_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2151_ = v_snd_2143_;
v_isShared_2152_ = v_isSharedCheck_2162_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snd_2149_);
lean_inc(v_fst_2148_);
lean_dec(v_snd_2143_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2162_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_fst_2148_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_snd_2149_);
v___x_2154_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2156_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v___x_2154_);
v___x_2156_ = v___x_2146_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_fst_2144_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
size_t v___x_2157_; size_t v___x_2158_; 
v___x_2157_ = ((size_t)1ULL);
v___x_2158_ = lean_usize_add(v_i_2122_, v___x_2157_);
v_i_2122_ = v___x_2158_;
v_b_2123_ = v___x_2156_;
goto _start;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg___boxed(lean_object* v_as_2168_, lean_object* v_sz_2169_, lean_object* v_i_2170_, lean_object* v_b_2171_){
_start:
{
size_t v_sz_boxed_2172_; size_t v_i_boxed_2173_; lean_object* v_res_2174_; 
v_sz_boxed_2172_ = lean_unbox_usize(v_sz_2169_);
lean_dec(v_sz_2169_);
v_i_boxed_2173_ = lean_unbox_usize(v_i_2170_);
lean_dec(v_i_2170_);
v_res_2174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(v_as_2168_, v_sz_boxed_2172_, v_i_boxed_2173_, v_b_2171_);
lean_dec_ref(v_as_2168_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(size_t v_sz_2175_, size_t v_i_2176_, lean_object* v_bs_2177_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_usize_dec_lt(v_i_2176_, v_sz_2175_);
if (v___x_2178_ == 0)
{
return v_bs_2177_;
}
else
{
lean_object* v_v_2179_; lean_object* v_snd_2180_; lean_object* v_fst_2181_; lean_object* v_fst_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2195_; 
v_v_2179_ = lean_array_uget_borrowed(v_bs_2177_, v_i_2176_);
v_snd_2180_ = lean_ctor_get(v_v_2179_, 1);
lean_inc(v_snd_2180_);
v_fst_2181_ = lean_ctor_get(v_v_2179_, 0);
lean_inc(v_fst_2181_);
v_fst_2182_ = lean_ctor_get(v_snd_2180_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_snd_2180_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; 
v_unused_2196_ = lean_ctor_get(v_snd_2180_, 1);
lean_dec(v_unused_2196_);
v___x_2184_ = v_snd_2180_;
v_isShared_2185_ = v_isSharedCheck_2195_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_fst_2182_);
lean_dec(v_snd_2180_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2195_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v_bs_x27_2187_; lean_object* v___x_2189_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v_bs_x27_2187_ = lean_array_uset(v_bs_2177_, v_i_2176_, v___x_2186_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 1, v_fst_2182_);
lean_ctor_set(v___x_2184_, 0, v_fst_2181_);
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_fst_2181_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_fst_2182_);
v___x_2189_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
size_t v___x_2190_; size_t v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((size_t)1ULL);
v___x_2191_ = lean_usize_add(v_i_2176_, v___x_2190_);
v___x_2192_ = lean_array_uset(v_bs_x27_2187_, v_i_2176_, v___x_2189_);
v_i_2176_ = v___x_2191_;
v_bs_2177_ = v___x_2192_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg___boxed(lean_object* v_sz_2197_, lean_object* v_i_2198_, lean_object* v_bs_2199_){
_start:
{
size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2197_);
lean_dec(v_sz_2197_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2198_);
lean_dec(v_i_2198_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(v_sz_boxed_2200_, v_i_boxed_2201_, v_bs_2199_);
return v_res_2202_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_unsigned_to_nat(16u);
v___x_2205_ = lean_mk_array(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_idx_2208_; 
v___x_2206_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0);
v___x_2207_ = lean_unsigned_to_nat(0u);
v_idx_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_idx_2208_, 0, v___x_2207_);
lean_ctor_set(v_idx_2208_, 1, v___x_2206_);
return v_idx_2208_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4(void){
_start:
{
lean_object* v___x_2214_; lean_object* v_idx_2215_; lean_object* v___x_2216_; 
v___x_2214_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__3));
v_idx_2215_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_idx_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(lean_object* v_ts_2217_){
_start:
{
lean_object* v___y_2219_; lean_object* v___x_2223_; lean_object* v___x_2224_; size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; lean_object* v_snd_2228_; lean_object* v_fst_2229_; lean_object* v___x_2230_; lean_object* v___y_2232_; lean_object* v___y_2233_; uint8_t v___x_2235_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4);
v_sz_2225_ = lean_array_size(v_ts_2217_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(v_ts_2217_, v_sz_2225_, v___x_2226_, v___x_2224_);
v_snd_2228_ = lean_ctor_get(v___x_2227_, 1);
lean_inc(v_snd_2228_);
lean_dec_ref(v___x_2227_);
v_fst_2229_ = lean_ctor_get(v_snd_2228_, 0);
lean_inc(v_fst_2229_);
lean_dec(v_snd_2228_);
v___x_2230_ = lean_array_get_size(v_fst_2229_);
v___x_2235_ = lean_nat_dec_eq(v___x_2230_, v___x_2223_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___y_2239_; uint8_t v___x_2241_; 
v___x_2236_ = lean_unsigned_to_nat(1u);
v___x_2237_ = lean_nat_sub(v___x_2230_, v___x_2236_);
v___x_2241_ = lean_nat_dec_le(v___x_2223_, v___x_2237_);
if (v___x_2241_ == 0)
{
lean_inc(v___x_2237_);
v___y_2239_ = v___x_2237_;
goto v___jp_2238_;
}
else
{
v___y_2239_ = v___x_2223_;
goto v___jp_2238_;
}
v___jp_2238_:
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_nat_dec_le(v___y_2239_, v___x_2237_);
if (v___x_2240_ == 0)
{
lean_dec(v___x_2237_);
lean_inc(v___y_2239_);
v___y_2232_ = v___y_2239_;
v___y_2233_ = v___y_2239_;
goto v___jp_2231_;
}
else
{
v___y_2232_ = v___y_2239_;
v___y_2233_ = v___x_2237_;
goto v___jp_2231_;
}
}
}
else
{
v___y_2219_ = v_fst_2229_;
goto v___jp_2218_;
}
v___jp_2218_:
{
size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_2222_; 
v_sz_2220_ = lean_array_size(v___y_2219_);
v___x_2221_ = ((size_t)0ULL);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(v_sz_2220_, v___x_2221_, v___y_2219_);
return v___x_2222_;
}
v___jp_2231_:
{
lean_object* v___x_2234_; 
v___x_2234_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(v___x_2230_, v_fst_2229_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
v___y_2219_ = v___x_2234_;
goto v___jp_2218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___boxed(lean_object* v_ts_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(v_ts_2242_);
lean_dec_ref(v_ts_2242_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey(lean_object* v_00_u03b1_2244_, lean_object* v_ts_2245_, lean_object* v_P_2246_, lean_object* v_hP_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(v_ts_2245_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___boxed(lean_object* v_00_u03b1_2249_, lean_object* v_ts_2250_, lean_object* v_P_2251_, lean_object* v_hP_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey(v_00_u03b1_2249_, v_ts_2250_, v_P_2251_, v_hP_2252_);
lean_dec_ref(v_ts_2250_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0(lean_object* v_00_u03b1_2254_, size_t v_sz_2255_, size_t v_i_2256_, lean_object* v_bs_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(v_sz_2255_, v_i_2256_, v_bs_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___boxed(lean_object* v_00_u03b1_2259_, lean_object* v_sz_2260_, lean_object* v_i_2261_, lean_object* v_bs_2262_){
_start:
{
size_t v_sz_boxed_2263_; size_t v_i_boxed_2264_; lean_object* v_res_2265_; 
v_sz_boxed_2263_ = lean_unbox_usize(v_sz_2260_);
lean_dec(v_sz_2260_);
v_i_boxed_2264_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_res_2265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0(v_00_u03b1_2259_, v_sz_boxed_2263_, v_i_boxed_2264_, v_bs_2262_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1(lean_object* v_00_u03b2_2266_, lean_object* v_m_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(v_m_2267_, v_a_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___boxed(lean_object* v_00_u03b2_2270_, lean_object* v_m_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1(v_00_u03b2_2270_, v_m_2271_, v_a_2272_);
lean_dec(v_a_2272_);
lean_dec_ref(v_m_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2(lean_object* v_00_u03b2_2274_, lean_object* v_m_2275_, lean_object* v_a_2276_, lean_object* v_b_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2___redArg(v_m_2275_, v_a_2276_, v_b_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3(lean_object* v_00_u03b1_2279_, lean_object* v_as_2280_, size_t v_sz_2281_, size_t v_i_2282_, lean_object* v_b_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(v_as_2280_, v_sz_2281_, v_i_2282_, v_b_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_as_2286_, lean_object* v_sz_2287_, lean_object* v_i_2288_, lean_object* v_b_2289_){
_start:
{
size_t v_sz_boxed_2290_; size_t v_i_boxed_2291_; lean_object* v_res_2292_; 
v_sz_boxed_2290_ = lean_unbox_usize(v_sz_2287_);
lean_dec(v_sz_2287_);
v_i_boxed_2291_ = lean_unbox_usize(v_i_2288_);
lean_dec(v_i_2288_);
v_res_2292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3(v_00_u03b1_2285_, v_as_2286_, v_sz_boxed_2290_, v_i_boxed_2291_, v_b_2289_);
lean_dec_ref(v_as_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4(lean_object* v_00_u03b1_2293_, lean_object* v_as_2294_, size_t v_sz_2295_, size_t v_i_2296_, lean_object* v_b_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(v_as_2294_, v_sz_2295_, v_i_2296_, v_b_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_as_2300_, lean_object* v_sz_2301_, lean_object* v_i_2302_, lean_object* v_b_2303_){
_start:
{
size_t v_sz_boxed_2304_; size_t v_i_boxed_2305_; lean_object* v_res_2306_; 
v_sz_boxed_2304_ = lean_unbox_usize(v_sz_2301_);
lean_dec(v_sz_2301_);
v_i_boxed_2305_ = lean_unbox_usize(v_i_2302_);
lean_dec(v_i_2302_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4(v_00_u03b1_2299_, v_as_2300_, v_sz_boxed_2304_, v_i_boxed_2305_, v_b_2303_);
lean_dec_ref(v_as_2300_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5(lean_object* v_00_u03b1_2307_, lean_object* v_n_2308_, lean_object* v_as_2309_, lean_object* v_lo_2310_, lean_object* v_hi_2311_, lean_object* v_w_2312_, lean_object* v_hlo_2313_, lean_object* v_hhi_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(v_n_2308_, v_as_2309_, v_lo_2310_, v_hi_2311_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___boxed(lean_object* v_00_u03b1_2316_, lean_object* v_n_2317_, lean_object* v_as_2318_, lean_object* v_lo_2319_, lean_object* v_hi_2320_, lean_object* v_w_2321_, lean_object* v_hlo_2322_, lean_object* v_hhi_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5(v_00_u03b1_2316_, v_n_2317_, v_as_2318_, v_lo_2319_, v_hi_2320_, v_w_2321_, v_hlo_2322_, v_hhi_2323_);
lean_dec(v_hi_2320_);
lean_dec(v_n_2317_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1(lean_object* v_00_u03b2_2325_, lean_object* v_a_2326_, lean_object* v_x_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(v_a_2326_, v_x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2329_, lean_object* v_a_2330_, lean_object* v_x_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1(v_00_u03b2_2329_, v_a_2330_, v_x_2331_);
lean_dec(v_x_2331_);
lean_dec(v_a_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3(lean_object* v_00_u03b2_2333_, lean_object* v_a_2334_, lean_object* v_x_2335_){
_start:
{
uint8_t v___x_2336_; 
v___x_2336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(v_a_2334_, v_x_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2337_, lean_object* v_a_2338_, lean_object* v_x_2339_){
_start:
{
uint8_t v_res_2340_; lean_object* v_r_2341_; 
v_res_2340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3(v_00_u03b2_2337_, v_a_2338_, v_x_2339_);
lean_dec(v_x_2339_);
lean_dec(v_a_2338_);
v_r_2341_ = lean_box(v_res_2340_);
return v_r_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4(lean_object* v_00_u03b2_2342_, lean_object* v_data_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4___redArg(v_data_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5(lean_object* v_00_u03b2_2345_, lean_object* v_a_2346_, lean_object* v_b_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(v_a_2346_, v_b_2347_, v_x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9(lean_object* v_00_u03b1_2350_, lean_object* v_n_2351_, lean_object* v_lo_2352_, lean_object* v_hi_2353_, lean_object* v_hhi_2354_, lean_object* v_pivot_2355_, lean_object* v_as_2356_, lean_object* v_i_2357_, lean_object* v_k_2358_, lean_object* v_ilo_2359_, lean_object* v_ik_2360_, lean_object* v_w_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(v_hi_2353_, v_pivot_2355_, v_as_2356_, v_i_2357_, v_k_2358_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2363_, lean_object* v_n_2364_, lean_object* v_lo_2365_, lean_object* v_hi_2366_, lean_object* v_hhi_2367_, lean_object* v_pivot_2368_, lean_object* v_as_2369_, lean_object* v_i_2370_, lean_object* v_k_2371_, lean_object* v_ilo_2372_, lean_object* v_ik_2373_, lean_object* v_w_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9(v_00_u03b1_2363_, v_n_2364_, v_lo_2365_, v_hi_2366_, v_hhi_2367_, v_pivot_2368_, v_as_2369_, v_i_2370_, v_k_2371_, v_ilo_2372_, v_ik_2373_, v_w_2374_);
lean_dec_ref(v_pivot_2368_);
lean_dec(v_hi_2366_);
lean_dec(v_lo_2365_);
lean_dec(v_n_2364_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2376_, lean_object* v_i_2377_, lean_object* v_source_2378_, lean_object* v_target_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5___redArg(v_i_2377_, v_source_2378_, v_target_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9___redArg(v_x_2382_, v_x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0(lean_object* v_x_2385_){
_start:
{
lean_object* v_snd_2386_; 
v_snd_2386_ = lean_ctor_get(v_x_2385_, 1);
lean_inc(v_snd_2386_);
return v_snd_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0___boxed(lean_object* v_x_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0(v_x_2387_);
lean_dec_ref(v_x_2387_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__4(lean_object* v___f_2389_, lean_object* v_x1_2390_, lean_object* v_x2_2391_){
_start:
{
lean_object* v_fst_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v_fst_2392_ = lean_ctor_get(v_x2_2391_, 0);
lean_inc(v_fst_2392_);
lean_dec_ref(v_x2_2391_);
v___x_2393_ = lean_array_get_size(v_x1_2390_);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_nat_dec_eq(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2396_ = lean_array_get_size(v_fst_2392_);
v___x_2397_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v___x_2398_ = lean_nat_dec_lt(v___x_2394_, v___x_2396_);
if (v___x_2398_ == 0)
{
lean_dec(v_fst_2392_);
lean_dec_ref(v___f_2389_);
return v_x1_2390_;
}
else
{
size_t v___x_2399_; size_t v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = ((size_t)0ULL);
v___x_2400_ = lean_usize_of_nat(v___x_2396_);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2397_, v___f_2389_, v_fst_2392_, v___x_2399_, v___x_2400_, v_x1_2390_);
return v___x_2401_;
}
}
else
{
lean_dec_ref(v_x1_2390_);
lean_dec_ref(v___f_2389_);
return v_fst_2392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__3(lean_object* v_inst_2402_, lean_object* v_x1_2403_, lean_object* v_x2_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_2402_, v_x1_2403_, v_x2_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2(lean_object* v_x1_2406_, lean_object* v_x2_2407_){
_start:
{
lean_object* v_fst_2408_; lean_object* v_fst_2409_; uint8_t v___x_2410_; 
v_fst_2408_ = lean_ctor_get(v_x1_2406_, 0);
v_fst_2409_ = lean_ctor_get(v_x2_2407_, 0);
v___x_2410_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_2408_, v_fst_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2___boxed(lean_object* v_x1_2411_, lean_object* v_x2_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2(v_x1_2411_, v_x2_2412_);
lean_dec_ref(v_x2_2412_);
lean_dec_ref(v_x1_2411_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(lean_object* v_inst_2417_, lean_object* v_g_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2419_ = lean_array_get_size(v_g_2418_);
v___x_2420_ = lean_unsigned_to_nat(1u);
v___x_2421_ = lean_nat_dec_eq(v___x_2419_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___f_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___f_2422_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2422_, 0, v_inst_2417_);
lean_closure_set(v___f_2422_, 1, v_g_2418_);
v___x_2423_ = lean_mk_thunk(v___f_2422_);
v___x_2424_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec_ref(v_inst_2417_);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_array_fget(v_g_2418_, v___x_2425_);
lean_dec_ref(v_g_2418_);
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__1(lean_object* v_inst_2427_, lean_object* v_x_2428_){
_start:
{
lean_object* v_fst_2429_; lean_object* v_snd_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2438_; 
v_fst_2429_ = lean_ctor_get(v_x_2428_, 0);
v_snd_2430_ = lean_ctor_get(v_x_2428_, 1);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2432_ = v_x_2428_;
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_snd_2430_);
lean_inc(v_fst_2429_);
lean_dec(v_x_2428_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(v_inst_2427_, v_snd_2430_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v___x_2434_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_fst_2429_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg(lean_object* v_inst_2440_, lean_object* v_ts_2441_){
_start:
{
lean_object* v___f_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; size_t v_sz_2447_; size_t v___x_2448_; lean_object* v_nodes_2449_; lean_object* v___x_2450_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2490_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___f_2442_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__0));
v___f_2443_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__1));
lean_inc_ref(v_inst_2440_);
v___f_2444_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2444_, 0, v_inst_2440_);
v___f_2445_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__2));
v___x_2446_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v_sz_2447_ = lean_array_size(v_ts_2441_);
v___x_2448_ = ((size_t)0ULL);
v_nodes_2449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2446_, v___f_2442_, v_sz_2447_, v___x_2448_, v_ts_2441_);
v___x_2450_ = lean_unsigned_to_nat(0u);
v___x_2499_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
v___x_2500_ = lean_array_get_size(v_nodes_2449_);
v___x_2501_ = lean_nat_dec_lt(v___x_2450_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_dec_ref(v_inst_2440_);
v___y_2490_ = v___x_2499_;
goto v___jp_2489_;
}
else
{
lean_object* v___f_2502_; lean_object* v___f_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v___f_2502_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__3), 3, 1);
lean_closure_set(v___f_2502_, 0, v_inst_2440_);
v___f_2503_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__4), 3, 1);
lean_closure_set(v___f_2503_, 0, v___f_2502_);
v___x_2504_ = lean_usize_of_nat(v___x_2500_);
lean_inc(v_nodes_2449_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2446_, v___f_2503_, v_nodes_2449_, v___x_2448_, v___x_2504_, v___x_2499_);
v___y_2490_ = v___x_2505_;
goto v___jp_2489_;
}
v___jp_2451_:
{
size_t v_sz_2455_; lean_object* v_cs_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_sz_2455_ = lean_array_size(v___y_2454_);
v_cs_2456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2446_, v___f_2444_, v_sz_2455_, v___x_2448_, v___y_2454_);
v___x_2457_ = lean_array_get_size(v___y_2453_);
v___x_2458_ = lean_nat_dec_eq(v___x_2457_, v___x_2450_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___y_2453_);
lean_ctor_set(v___x_2459_, 1, v_cs_2456_);
return v___x_2459_;
}
else
{
lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2460_ = lean_array_get_size(v_cs_2456_);
v___x_2461_ = lean_nat_dec_eq(v___x_2460_, v___y_2452_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___y_2453_);
lean_ctor_set(v___x_2462_, 1, v_cs_2456_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v___y_2453_);
v___x_2463_ = lean_array_fget(v_cs_2456_, v___x_2450_);
lean_dec(v_cs_2456_);
v_fst_2464_ = lean_ctor_get(v___x_2463_, 0);
v_snd_2465_ = lean_ctor_get(v___x_2463_, 1);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2463_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snd_2465_);
lean_inc(v_fst_2464_);
lean_dec(v___x_2463_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_fst_2464_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_snd_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
v___jp_2473_:
{
lean_object* v___x_2480_; 
v___x_2480_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2445_, v___y_2475_, v___y_2477_, v___y_2474_, v___y_2479_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2479_);
lean_dec(v___y_2475_);
v___y_2452_ = v___y_2476_;
v___y_2453_ = v___y_2478_;
v___y_2454_ = v___x_2480_;
goto v___jp_2451_;
}
v___jp_2481_:
{
uint8_t v___x_2488_; 
v___x_2488_ = lean_nat_dec_le(v___y_2487_, v___y_2485_);
if (v___x_2488_ == 0)
{
lean_dec(v___y_2485_);
lean_inc(v___y_2487_);
v___y_2474_ = v___y_2487_;
v___y_2475_ = v___y_2482_;
v___y_2476_ = v___y_2483_;
v___y_2477_ = v___y_2484_;
v___y_2478_ = v___y_2486_;
v___y_2479_ = v___y_2487_;
goto v___jp_2473_;
}
else
{
v___y_2474_ = v___y_2487_;
v___y_2475_ = v___y_2482_;
v___y_2476_ = v___y_2483_;
v___y_2477_ = v___y_2484_;
v___y_2478_ = v___y_2486_;
v___y_2479_ = v___y_2485_;
goto v___jp_2473_;
}
}
v___jp_2489_:
{
size_t v_sz_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_sz_2491_ = lean_array_size(v_nodes_2449_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2446_, v___f_2443_, v_sz_2491_, v___x_2448_, v_nodes_2449_);
v___x_2493_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(v___x_2492_);
lean_dec(v___x_2492_);
v___x_2494_ = lean_unsigned_to_nat(1u);
v___x_2495_ = lean_array_get_size(v___x_2493_);
v___x_2496_ = lean_nat_dec_eq(v___x_2495_, v___x_2450_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2497_ = lean_nat_sub(v___x_2495_, v___x_2494_);
v___x_2498_ = lean_nat_dec_le(v___x_2450_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_inc(v___x_2497_);
v___y_2482_ = v___x_2495_;
v___y_2483_ = v___x_2494_;
v___y_2484_ = v___x_2493_;
v___y_2485_ = v___x_2497_;
v___y_2486_ = v___y_2490_;
v___y_2487_ = v___x_2497_;
goto v___jp_2481_;
}
else
{
v___y_2482_ = v___x_2495_;
v___y_2483_ = v___x_2494_;
v___y_2484_ = v___x_2493_;
v___y_2485_ = v___x_2497_;
v___y_2486_ = v___y_2490_;
v___y_2487_ = v___x_2450_;
goto v___jp_2481_;
}
}
else
{
v___y_2452_ = v___x_2494_;
v___y_2453_ = v___y_2490_;
v___y_2454_ = v___x_2493_;
goto v___jp_2451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg___lam__0(lean_object* v_inst_2506_, lean_object* v_g_2507_, lean_object* v_x_2508_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg(v_inst_2506_, v_g_2507_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries(lean_object* v_00_u03b1_2510_, lean_object* v_inst_2511_, lean_object* v_ts_2512_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg(v_inst_2511_, v_ts_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup(lean_object* v_00_u03b1_2514_, lean_object* v_inst_2515_, lean_object* v_g_2516_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(v_inst_2515_, v_g_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries_match__1_splitter___redArg(lean_object* v_x_2518_, lean_object* v_h__1_2519_){
_start:
{
lean_object* v_fst_2520_; lean_object* v_snd_2521_; lean_object* v___x_2522_; 
v_fst_2520_ = lean_ctor_get(v_x_2518_, 0);
lean_inc(v_fst_2520_);
v_snd_2521_ = lean_ctor_get(v_x_2518_, 1);
lean_inc(v_snd_2521_);
lean_dec_ref(v_x_2518_);
v___x_2522_ = lean_apply_2(v_h__1_2519_, v_fst_2520_, v_snd_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries_match__1_splitter(lean_object* v_00_u03b1_2523_, lean_object* v_motive_2524_, lean_object* v_x_2525_, lean_object* v_h__1_2526_){
_start:
{
lean_object* v_fst_2527_; lean_object* v_snd_2528_; lean_object* v___x_2529_; 
v_fst_2527_ = lean_ctor_get(v_x_2525_, 0);
lean_inc(v_fst_2527_);
v_snd_2528_ = lean_ctor_get(v_x_2525_, 1);
lean_inc(v_snd_2528_);
lean_dec_ref(v_x_2525_);
v___x_2529_ = lean_apply_2(v_h__1_2526_, v_fst_2527_, v_snd_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0(lean_object* v_inst_2530_, lean_object* v___x_2531_, lean_object* v___x_2532_, lean_object* v___x_2533_, lean_object* v_a_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_snd_2537_; lean_object* v_fst_2538_; lean_object* v_snd_2539_; lean_object* v_fst_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2566_; 
v_snd_2537_ = lean_ctor_get(v___y_2536_, 1);
lean_inc(v_snd_2537_);
v_fst_2538_ = lean_ctor_get(v_a_2534_, 0);
lean_inc(v_fst_2538_);
v_snd_2539_ = lean_ctor_get(v_a_2534_, 1);
lean_inc(v_snd_2539_);
lean_dec_ref(v_a_2534_);
v_fst_2540_ = lean_ctor_get(v___y_2536_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___y_2536_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v___y_2536_, 1);
lean_dec(v_unused_2567_);
v___x_2542_ = v___y_2536_;
v_isShared_2543_ = v_isSharedCheck_2566_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_fst_2540_);
lean_dec(v___y_2536_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2566_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v_fst_2544_; lean_object* v_snd_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2565_; 
v_fst_2544_ = lean_ctor_get(v_snd_2537_, 0);
v_snd_2545_ = lean_ctor_get(v_snd_2537_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_snd_2537_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2547_ = v_snd_2537_;
v_isShared_2548_ = v_isSharedCheck_2565_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_snd_2545_);
lean_inc(v_fst_2544_);
lean_dec(v_snd_2537_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2565_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_last_2550_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v___x_2561_ = lean_array_get_size(v_fst_2538_);
v___x_2562_ = lean_nat_dec_lt(v___x_2531_, v___x_2561_);
if (v___x_2562_ == 0)
{
lean_dec_ref(v___x_2533_);
lean_dec_ref(v___x_2532_);
v_last_2550_ = v_fst_2544_;
goto v___jp_2549_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_array_fget_borrowed(v_fst_2538_, v___x_2531_);
lean_inc(v_snd_2545_);
lean_inc(v___x_2563_);
v___x_2564_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2532_, v___x_2533_, v_fst_2544_, v___x_2563_, v_snd_2545_);
v_last_2550_ = v___x_2564_;
goto v___jp_2549_;
}
v___jp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2551_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_2530_, v_fst_2540_, v_fst_2538_, v_snd_2539_);
v___x_2552_ = lean_unsigned_to_nat(1u);
v___x_2553_ = lean_nat_add(v_snd_2545_, v___x_2552_);
lean_dec(v_snd_2545_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 1, v___x_2553_);
lean_ctor_set(v___x_2547_, 0, v_last_2550_);
v___x_2555_ = v___x_2547_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_last_2550_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 1, v___x_2555_);
lean_ctor_set(v___x_2542_, 0, v___x_2551_);
v___x_2557_ = v___x_2542_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0___boxed(lean_object* v_inst_2568_, lean_object* v___x_2569_, lean_object* v___x_2570_, lean_object* v___x_2571_, lean_object* v_a_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0(v_inst_2568_, v___x_2569_, v___x_2570_, v___x_2571_, v_a_2572_, v_x_2573_, v___y_2574_);
lean_dec(v___x_2569_);
return v_res_2575_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1(lean_object* v_x1_2576_, lean_object* v_x2_2577_){
_start:
{
lean_object* v_snd_2578_; lean_object* v_snd_2579_; uint8_t v___x_2580_; 
v_snd_2578_ = lean_ctor_get(v_x1_2576_, 1);
v_snd_2579_ = lean_ctor_get(v_x2_2577_, 1);
v___x_2580_ = lean_nat_dec_lt(v_snd_2578_, v_snd_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1___boxed(lean_object* v_x1_2581_, lean_object* v_x2_2582_){
_start:
{
uint8_t v_res_2583_; lean_object* v_r_2584_; 
v_res_2583_ = l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1(v_x1_2581_, v_x2_2582_);
lean_dec_ref(v_x2_2582_);
lean_dec_ref(v_x1_2581_);
v_r_2584_ = lean_box(v_res_2583_);
return v_r_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2(lean_object* v___x_2585_, lean_object* v___x_2586_, lean_object* v_fst_2587_, lean_object* v___x_2588_, lean_object* v_x_2589_){
_start:
{
lean_object* v_fst_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2604_; 
v_fst_2590_ = lean_ctor_get(v_x_2589_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_x_2589_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v_x_2589_, 1);
lean_dec(v_unused_2605_);
v___x_2592_ = v_x_2589_;
v_isShared_2593_ = v_isSharedCheck_2604_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_fst_2590_);
lean_dec(v_x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2604_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; 
lean_inc(v_fst_2590_);
v___x_2594_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2585_, v___x_2586_, v_fst_2587_, v_fst_2590_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = lean_mk_empty_array_with_capacity(v___x_2588_);
lean_inc_ref(v___x_2595_);
v___x_2596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v___x_2596_);
v___x_2598_ = v___x_2592_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_fst_2590_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
else
{
lean_object* v_val_2600_; lean_object* v___x_2602_; 
v_val_2600_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_val_2600_);
lean_dec_ref_known(v___x_2594_, 1);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v_val_2600_);
v___x_2602_ = v___x_2592_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_fst_2590_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_val_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2___boxed(lean_object* v___x_2606_, lean_object* v___x_2607_, lean_object* v_fst_2608_, lean_object* v___x_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2(v___x_2606_, v___x_2607_, v_fst_2608_, v___x_2609_, v_x_2610_);
lean_dec(v___x_2609_);
lean_dec(v_fst_2608_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__3(lean_object* v_x1_2612_, lean_object* v_x2_2613_, lean_object* v_x3_2614_){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v_x2_2613_);
lean_ctor_set(v___x_2615_, 1, v_x3_2614_);
v___x_2616_ = lean_array_push(v_x1_2612_, v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__4(lean_object* v___x_2617_, lean_object* v___f_2618_, lean_object* v_acc_2619_, lean_object* v_l_2620_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_2617_, v___f_2618_, v_acc_2619_, v_l_2620_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_2622_; lean_object* v_last_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_unsigned_to_nat(0u);
v_last_2623_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v_last_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2622_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1(void){
_start:
{
lean_object* v___x_2625_; lean_object* v_d_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_obj_once(&l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0, &l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0_once, _init_l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0);
v_d_2626_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_d_2626_);
lean_ctor_set(v___x_2627_, 1, v___x_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg(lean_object* v_inst_2633_, lean_object* v_entries_2634_){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; size_t v_sz_2641_; size_t v___x_2642_; lean_object* v___x_2643_; lean_object* v_snd_2644_; lean_object* v_fst_2645_; lean_object* v_fst_2646_; lean_object* v_size_2647_; lean_object* v_buckets_2648_; lean_object* v___f_2649_; lean_object* v___f_2650_; lean_object* v___y_2652_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2668_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2635_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0));
v___x_2636_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1));
v___x_2637_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v___x_2638_ = lean_unsigned_to_nat(0u);
v___f_2639_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2639_, 0, v_inst_2633_);
lean_closure_set(v___f_2639_, 1, v___x_2638_);
lean_closure_set(v___f_2639_, 2, v___x_2635_);
lean_closure_set(v___f_2639_, 3, v___x_2636_);
v___x_2640_ = lean_obj_once(&l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1, &l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1);
v_sz_2641_ = lean_array_size(v_entries_2634_);
v___x_2642_ = ((size_t)0ULL);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2637_, v_entries_2634_, v___f_2639_, v_sz_2641_, v___x_2642_, v___x_2640_);
v_snd_2644_ = lean_ctor_get(v___x_2643_, 1);
v_fst_2645_ = lean_ctor_get(v_snd_2644_, 0);
lean_inc(v_fst_2645_);
v_fst_2646_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_fst_2646_);
lean_dec(v___x_2643_);
v_size_2647_ = lean_ctor_get(v_fst_2645_, 0);
lean_inc(v_size_2647_);
v_buckets_2648_ = lean_ctor_get(v_fst_2645_, 1);
lean_inc_ref(v_buckets_2648_);
lean_dec(v_fst_2645_);
v___f_2649_ = ((lean_object*)(l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__2));
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2650_, 0, v___x_2635_);
lean_closure_set(v___f_2650_, 1, v___x_2636_);
lean_closure_set(v___f_2650_, 2, v_fst_2646_);
lean_closure_set(v___f_2650_, 3, v___x_2638_);
v___x_2674_ = lean_mk_empty_array_with_capacity(v_size_2647_);
lean_dec(v_size_2647_);
v___x_2675_ = lean_array_get_size(v_buckets_2648_);
v___x_2676_ = lean_nat_dec_lt(v___x_2638_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_dec_ref(v_buckets_2648_);
v___y_2668_ = v___x_2674_;
goto v___jp_2667_;
}
else
{
lean_object* v___f_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
v___f_2677_ = ((lean_object*)(l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__4));
v___x_2678_ = lean_usize_of_nat(v___x_2675_);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2637_, v___f_2677_, v_buckets_2648_, v___x_2642_, v___x_2678_, v___x_2674_);
v___y_2668_ = v___x_2679_;
goto v___jp_2667_;
}
v___jp_2651_:
{
size_t v_sz_2653_; lean_object* v___x_2654_; 
v_sz_2653_ = lean_array_size(v___y_2652_);
v___x_2654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2637_, v___f_2650_, v_sz_2653_, v___x_2642_, v___y_2652_);
return v___x_2654_;
}
v___jp_2655_:
{
lean_object* v___x_2660_; 
v___x_2660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2649_, v___y_2657_, v___y_2656_, v___y_2658_, v___y_2659_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2659_);
lean_dec(v___y_2657_);
v___y_2652_ = v___x_2660_;
goto v___jp_2651_;
}
v___jp_2661_:
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_nat_dec_le(v___y_2665_, v___y_2662_);
if (v___x_2666_ == 0)
{
lean_dec(v___y_2662_);
lean_inc(v___y_2665_);
v___y_2656_ = v___y_2664_;
v___y_2657_ = v___y_2663_;
v___y_2658_ = v___y_2665_;
v___y_2659_ = v___y_2665_;
goto v___jp_2655_;
}
else
{
v___y_2656_ = v___y_2664_;
v___y_2657_ = v___y_2663_;
v___y_2658_ = v___y_2665_;
v___y_2659_ = v___y_2662_;
goto v___jp_2655_;
}
}
v___jp_2667_:
{
lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = lean_array_get_size(v___y_2668_);
v___x_2670_ = lean_nat_dec_eq(v___x_2669_, v___x_2638_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = lean_nat_sub(v___x_2669_, v___x_2671_);
v___x_2673_ = lean_nat_dec_le(v___x_2638_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_inc(v___x_2672_);
v___y_2662_ = v___x_2672_;
v___y_2663_ = v___x_2669_;
v___y_2664_ = v___y_2668_;
v___y_2665_ = v___x_2672_;
goto v___jp_2661_;
}
else
{
v___y_2662_ = v___x_2672_;
v___y_2663_ = v___x_2669_;
v___y_2664_ = v___y_2668_;
v___y_2665_ = v___x_2638_;
goto v___jp_2661_;
}
}
else
{
v___y_2652_ = v___y_2668_;
goto v___jp_2651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf(lean_object* v_00_u03b1_2680_, lean_object* v_inst_2681_, lean_object* v_entries_2682_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_Meta_DiscrTree_moduleRootsOf___redArg(v_inst_2681_, v_entries_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg___lam__0(lean_object* v_inst_2684_, lean_object* v___x_2685_, lean_object* v___x_2686_, lean_object* v_x1_2687_, lean_object* v_x2_2688_){
_start:
{
lean_object* v_fst_2689_; lean_object* v_snd_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_fst_2689_ = lean_ctor_get(v_x2_2688_, 0);
lean_inc(v_fst_2689_);
v_snd_2690_ = lean_ctor_get(v_x2_2688_, 1);
lean_inc(v_snd_2690_);
lean_dec_ref(v_x2_2688_);
v___x_2691_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(v_inst_2684_, v_snd_2690_);
v___x_2692_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2685_, v___x_2686_, v_x1_2687_, v_fst_2689_, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg(lean_object* v_inst_2693_, lean_object* v_mods_2694_){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2695_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1);
v___x_2696_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(v_mods_2694_);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = lean_array_get_size(v___x_2696_);
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v___x_2700_ = lean_nat_dec_lt(v___x_2697_, v___x_2698_);
if (v___x_2700_ == 0)
{
lean_dec_ref(v___x_2696_);
lean_dec_ref(v_inst_2693_);
return v___x_2695_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___f_2703_; size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v___x_2701_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0));
v___x_2702_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1));
v___f_2703_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_ofModuleRoots___redArg___lam__0), 5, 3);
lean_closure_set(v___f_2703_, 0, v_inst_2693_);
lean_closure_set(v___f_2703_, 1, v___x_2701_);
lean_closure_set(v___f_2703_, 2, v___x_2702_);
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = lean_usize_of_nat(v___x_2698_);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2699_, v___f_2703_, v___x_2696_, v___x_2704_, v___x_2705_, v___x_2695_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg___boxed(lean_object* v_inst_2707_, lean_object* v_mods_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Meta_DiscrTree_ofModuleRoots___redArg(v_inst_2707_, v_mods_2708_);
lean_dec_ref(v_mods_2708_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots(lean_object* v_00_u03b1_2710_, lean_object* v_inst_2711_, lean_object* v_mods_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_Meta_DiscrTree_ofModuleRoots___redArg(v_inst_2711_, v_mods_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_inst_2715_, lean_object* v_mods_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_DiscrTree_ofModuleRoots(v_00_u03b1_2714_, v_inst_2715_, v_mods_2716_);
lean_dec_ref(v_mods_2716_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___redArg(lean_object* v_inst_2718_, lean_object* v_d_2719_, lean_object* v_keys_2720_, lean_object* v_v_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_2718_, v_d_2719_, v_keys_2720_, v_v_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object* v_00_u03b1_2723_, lean_object* v_inst_2724_, lean_object* v_d_2725_, lean_object* v_keys_2726_, lean_object* v_v_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_2724_, v_d_2725_, v_keys_2726_, v_v_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(lean_object* v_as_2729_, lean_object* v_k_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v_m_2735_; lean_object* v_a_2736_; uint8_t v___x_2737_; 
v___x_2733_ = lean_nat_add(v_x_2731_, v_x_2732_);
v___x_2734_ = lean_unsigned_to_nat(1u);
v_m_2735_ = lean_nat_shiftr(v___x_2733_, v___x_2734_);
lean_dec(v___x_2733_);
v_a_2736_ = lean_array_fget_borrowed(v_as_2729_, v_m_2735_);
v___x_2737_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(v_a_2736_, v_k_2730_);
if (v___x_2737_ == 0)
{
uint8_t v___x_2738_; 
lean_dec(v_x_2732_);
v___x_2738_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(v_k_2730_, v_a_2736_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; 
lean_dec(v_m_2735_);
lean_dec(v_x_2731_);
lean_inc(v_a_2736_);
v___x_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_a_2736_);
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; uint8_t v___x_2741_; 
v___x_2740_ = lean_unsigned_to_nat(0u);
v___x_2741_ = lean_nat_dec_eq(v_m_2735_, v___x_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = lean_nat_sub(v_m_2735_, v___x_2734_);
lean_dec(v_m_2735_);
v___x_2743_ = lean_nat_dec_lt(v___x_2742_, v_x_2731_);
if (v___x_2743_ == 0)
{
v_x_2732_ = v___x_2742_;
goto _start;
}
else
{
lean_object* v___x_2745_; 
lean_dec(v___x_2742_);
lean_dec(v_x_2731_);
v___x_2745_ = lean_box(0);
return v___x_2745_;
}
}
else
{
lean_object* v___x_2746_; 
lean_dec(v_m_2735_);
lean_dec(v_x_2731_);
v___x_2746_ = lean_box(0);
return v___x_2746_;
}
}
}
else
{
lean_object* v___x_2747_; uint8_t v___x_2748_; 
lean_dec(v_x_2731_);
v___x_2747_ = lean_nat_add(v_m_2735_, v___x_2734_);
lean_dec(v_m_2735_);
v___x_2748_ = lean_nat_dec_le(v___x_2747_, v_x_2732_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
lean_dec(v___x_2747_);
lean_dec(v_x_2732_);
v___x_2749_ = lean_box(0);
return v___x_2749_;
}
else
{
v_x_2731_ = v___x_2747_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg___boxed(lean_object* v_as_2751_, lean_object* v_k_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(v_as_2751_, v_k_2752_, v_x_2753_, v_x_2754_);
lean_dec_ref(v_k_2752_);
lean_dec_ref(v_as_2751_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(lean_object* v_keys_2756_, lean_object* v_i_2757_, lean_object* v_t_2758_){
_start:
{
lean_object* v_val_2762_; 
switch(lean_obj_tag(v_t_2758_))
{
case 2:
{
lean_object* v___x_2798_; 
v___x_2798_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_2758_);
v_val_2762_ = v___x_2798_;
goto v___jp_2761_;
}
case 3:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_2758_);
v_val_2762_ = v___x_2799_;
goto v___jp_2761_;
}
default: 
{
v_val_2762_ = v_t_2758_;
goto v___jp_2761_;
}
}
v___jp_2759_:
{
lean_object* v___x_2760_; 
v___x_2760_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
return v___x_2760_;
}
v___jp_2761_:
{
if (lean_obj_tag(v_val_2762_) == 0)
{
lean_object* v_key_2763_; lean_object* v_child_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v_key_2763_ = lean_ctor_get(v_val_2762_, 0);
lean_inc(v_key_2763_);
v_child_2764_ = lean_ctor_get(v_val_2762_, 1);
lean_inc_ref(v_child_2764_);
lean_dec_ref_known(v_val_2762_, 2);
v___x_2765_ = lean_array_get_size(v_keys_2756_);
v___x_2766_ = lean_nat_dec_lt(v_i_2757_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
lean_dec_ref(v_child_2764_);
lean_dec(v_key_2763_);
lean_dec(v_i_2757_);
v___x_2767_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = lean_array_fget_borrowed(v_keys_2756_, v_i_2757_);
v___x_2769_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_2768_, v_key_2763_);
lean_dec(v_key_2763_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_dec_ref(v_child_2764_);
lean_dec(v_i_2757_);
v___x_2770_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_unsigned_to_nat(1u);
v___x_2772_ = lean_nat_add(v_i_2757_, v___x_2771_);
lean_dec(v_i_2757_);
v_i_2757_ = v___x_2772_;
v_t_2758_ = v_child_2764_;
goto _start;
}
}
}
else
{
lean_object* v_vs_2774_; lean_object* v_children_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2797_; 
v_vs_2774_ = lean_ctor_get(v_val_2762_, 0);
v_children_2775_ = lean_ctor_get(v_val_2762_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_val_2762_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2777_ = v_val_2762_;
v_isShared_2778_ = v_isSharedCheck_2797_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_children_2775_);
lean_inc(v_vs_2774_);
lean_dec(v_val_2762_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2797_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = lean_array_get_size(v_keys_2756_);
v___x_2780_ = lean_nat_dec_lt(v_i_2757_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_del_object(v___x_2777_);
lean_dec_ref(v_children_2775_);
lean_dec(v_i_2757_);
return v_vs_2774_;
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
lean_dec_ref(v_vs_2774_);
v___x_2781_ = lean_unsigned_to_nat(0u);
v___x_2782_ = lean_array_get_size(v_children_2775_);
v___x_2783_ = lean_nat_dec_lt(v___x_2781_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_del_object(v___x_2777_);
lean_dec_ref(v_children_2775_);
lean_dec(v_i_2757_);
goto v___jp_2759_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2784_ = lean_unsigned_to_nat(1u);
v___x_2785_ = lean_nat_sub(v___x_2782_, v___x_2784_);
v___x_2786_ = lean_nat_dec_le(v___x_2781_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_dec(v___x_2785_);
lean_del_object(v___x_2777_);
lean_dec_ref(v_children_2775_);
lean_dec(v_i_2757_);
goto v___jp_2759_;
}
else
{
lean_object* v_k_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v_k_2787_ = lean_array_fget_borrowed(v_keys_2756_, v_i_2757_);
v___x_2788_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1));
lean_inc(v_k_2787_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 0);
lean_ctor_set(v___x_2777_, 1, v___x_2788_);
lean_ctor_set(v___x_2777_, 0, v_k_2787_);
v___x_2790_ = v___x_2777_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_k_2787_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(v_children_2775_, v___x_2790_, v___x_2781_, v___x_2785_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_children_2775_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_dec(v_i_2757_);
goto v___jp_2759_;
}
else
{
lean_object* v_val_2792_; lean_object* v_snd_2793_; lean_object* v___x_2794_; 
v_val_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_val_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v_snd_2793_ = lean_ctor_get(v_val_2792_, 1);
lean_inc(v_snd_2793_);
lean_dec(v_val_2792_);
v___x_2794_ = lean_nat_add(v_i_2757_, v___x_2784_);
lean_dec(v_i_2757_);
v_i_2757_ = v___x_2794_;
v_t_2758_ = v_snd_2793_;
goto _start;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg___boxed(lean_object* v_keys_2800_, lean_object* v_i_2801_, lean_object* v_t_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(v_keys_2800_, v_i_2801_, v_t_2802_);
lean_dec_ref(v_keys_2800_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux(lean_object* v_00_u03b1_2804_, lean_object* v_keys_2805_, lean_object* v_i_2806_, lean_object* v_t_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(v_keys_2805_, v_i_2806_, v_t_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___boxed(lean_object* v_00_u03b1_2809_, lean_object* v_keys_2810_, lean_object* v_i_2811_, lean_object* v_t_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux(v_00_u03b1_2809_, v_keys_2810_, v_i_2811_, v_t_2812_);
lean_dec_ref(v_keys_2810_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0(lean_object* v_00_u03b1_2814_, lean_object* v_as_2815_, lean_object* v_k_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(v_as_2815_, v_k_2816_, v_x_2817_, v_x_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_as_2822_, lean_object* v_k_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0(v_00_u03b1_2821_, v_as_2822_, v_k_2823_, v_x_2824_, v_x_2825_, v_x_2826_);
lean_dec_ref(v_k_2823_);
lean_dec_ref(v_as_2822_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_match__1_splitter___redArg(lean_object* v_x_2828_, lean_object* v_h__1_2829_, lean_object* v_h__2_2830_){
_start:
{
if (lean_obj_tag(v_x_2828_) == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_dec(v_h__2_2830_);
v___x_2831_ = lean_box(0);
v___x_2832_ = lean_apply_1(v_h__1_2829_, v___x_2831_);
return v___x_2832_;
}
else
{
lean_object* v_val_2833_; lean_object* v_fst_2834_; lean_object* v_snd_2835_; lean_object* v___x_2836_; 
lean_dec(v_h__1_2829_);
v_val_2833_ = lean_ctor_get(v_x_2828_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v_x_2828_, 1);
v_fst_2834_ = lean_ctor_get(v_val_2833_, 0);
lean_inc(v_fst_2834_);
v_snd_2835_ = lean_ctor_get(v_val_2833_, 1);
lean_inc(v_snd_2835_);
lean_dec(v_val_2833_);
v___x_2836_ = lean_apply_2(v_h__2_2830_, v_fst_2834_, v_snd_2835_);
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_match__1_splitter(lean_object* v_00_u03b1_2837_, lean_object* v_motive_2838_, lean_object* v_x_2839_, lean_object* v_h__1_2840_, lean_object* v_h__2_2841_){
_start:
{
if (lean_obj_tag(v_x_2839_) == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec(v_h__2_2841_);
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_apply_1(v_h__1_2840_, v___x_2842_);
return v___x_2843_;
}
else
{
lean_object* v_val_2844_; lean_object* v_fst_2845_; lean_object* v_snd_2846_; lean_object* v___x_2847_; 
lean_dec(v_h__1_2840_);
v_val_2844_ = lean_ctor_get(v_x_2839_, 0);
lean_inc(v_val_2844_);
lean_dec_ref_known(v_x_2839_, 1);
v_fst_2845_ = lean_ctor_get(v_val_2844_, 0);
lean_inc(v_fst_2845_);
v_snd_2846_ = lean_ctor_get(v_val_2844_, 1);
lean_inc(v_snd_2846_);
lean_dec(v_val_2844_);
v___x_2847_ = lean_apply_2(v_h__2_2841_, v_fst_2845_, v_snd_2846_);
return v___x_2847_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1___redArg(lean_object* v_msg_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0, &l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0);
v___x_2850_ = lean_panic_fn_borrowed(v___x_2849_, v_msg_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1(lean_object* v_00_u03b1_2851_, lean_object* v_msg_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1___redArg(v_msg_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2854_, lean_object* v_vals_2855_, lean_object* v_i_2856_, lean_object* v_k_2857_){
_start:
{
lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2858_ = lean_array_get_size(v_keys_2854_);
v___x_2859_ = lean_nat_dec_lt(v_i_2856_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec(v_i_2856_);
v___x_2860_ = lean_box(0);
return v___x_2860_;
}
else
{
lean_object* v_k_x27_2861_; uint8_t v___x_2862_; 
v_k_x27_2861_ = lean_array_fget_borrowed(v_keys_2854_, v_i_2856_);
v___x_2862_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_2857_, v_k_x27_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_unsigned_to_nat(1u);
v___x_2864_ = lean_nat_add(v_i_2856_, v___x_2863_);
lean_dec(v_i_2856_);
v_i_2856_ = v___x_2864_;
goto _start;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_array_fget_borrowed(v_vals_2855_, v_i_2856_);
lean_dec(v_i_2856_);
lean_inc(v___x_2866_);
v___x_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2868_, lean_object* v_vals_2869_, lean_object* v_i_2870_, lean_object* v_k_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(v_keys_2868_, v_vals_2869_, v_i_2870_, v_k_2871_);
lean_dec(v_k_2871_);
lean_dec_ref(v_vals_2869_);
lean_dec_ref(v_keys_2868_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(lean_object* v_x_2873_, size_t v_x_2874_, lean_object* v_x_2875_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
lean_object* v_es_2876_; lean_object* v___x_2877_; size_t v___x_2878_; size_t v___x_2879_; lean_object* v_j_2880_; lean_object* v___x_2881_; 
v_es_2876_ = lean_ctor_get(v_x_2873_, 0);
v___x_2877_ = lean_box(2);
v___x_2878_ = ((size_t)31ULL);
v___x_2879_ = lean_usize_land(v_x_2874_, v___x_2878_);
v_j_2880_ = lean_usize_to_nat(v___x_2879_);
v___x_2881_ = lean_array_get_borrowed(v___x_2877_, v_es_2876_, v_j_2880_);
lean_dec(v_j_2880_);
switch(lean_obj_tag(v___x_2881_))
{
case 0:
{
lean_object* v_key_2882_; lean_object* v_val_2883_; uint8_t v___x_2884_; 
v_key_2882_ = lean_ctor_get(v___x_2881_, 0);
v_val_2883_ = lean_ctor_get(v___x_2881_, 1);
v___x_2884_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2875_, v_key_2882_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_box(0);
return v___x_2885_;
}
else
{
lean_object* v___x_2886_; 
lean_inc(v_val_2883_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_val_2883_);
return v___x_2886_;
}
}
case 1:
{
lean_object* v_node_2887_; size_t v___x_2888_; size_t v___x_2889_; 
v_node_2887_ = lean_ctor_get(v___x_2881_, 0);
v___x_2888_ = ((size_t)5ULL);
v___x_2889_ = lean_usize_shift_right(v_x_2874_, v___x_2888_);
v_x_2873_ = v_node_2887_;
v_x_2874_ = v___x_2889_;
goto _start;
}
default: 
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_box(0);
return v___x_2891_;
}
}
}
else
{
lean_object* v_ks_2892_; lean_object* v_vs_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_ks_2892_ = lean_ctor_get(v_x_2873_, 0);
v_vs_2893_ = lean_ctor_get(v_x_2873_, 1);
v___x_2894_ = lean_unsigned_to_nat(0u);
v___x_2895_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(v_ks_2892_, v_vs_2893_, v___x_2894_, v_x_2875_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg___boxed(lean_object* v_x_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_){
_start:
{
size_t v_x_233__boxed_2899_; lean_object* v_res_2900_; 
v_x_233__boxed_2899_ = lean_unbox_usize(v_x_2897_);
lean_dec(v_x_2897_);
v_res_2900_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(v_x_2896_, v_x_233__boxed_2899_, v_x_2898_);
lean_dec(v_x_2898_);
lean_dec_ref(v_x_2896_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(lean_object* v_x_2901_, lean_object* v_x_2902_){
_start:
{
uint64_t v___x_2903_; size_t v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2902_);
v___x_2904_ = lean_uint64_to_usize(v___x_2903_);
v___x_2905_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(v_x_2901_, v___x_2904_, v_x_2902_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg___boxed(lean_object* v_x_2906_, lean_object* v_x_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(v_x_2906_, v_x_2907_);
lean_dec(v_x_2907_);
lean_dec_ref(v_x_2906_);
return v_res_2908_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2910_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3));
v___x_2911_ = lean_unsigned_to_nat(23u);
v___x_2912_ = lean_unsigned_to_nat(385u);
v___x_2913_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__0));
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0));
v___x_2915_ = l_mkPanicMessageWithDecl(v___x_2914_, v___x_2913_, v___x_2912_, v___x_2911_, v___x_2910_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg(lean_object* v_d_2916_, lean_object* v_keys_2917_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2918_ = lean_array_get_size(v_keys_2917_);
v___x_2919_ = lean_unsigned_to_nat(0u);
v___x_2920_ = lean_nat_dec_eq(v___x_2918_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; lean_object* v_k_2922_; lean_object* v___x_2923_; 
v___x_2921_ = lean_box(0);
v_k_2922_ = lean_array_get_borrowed(v___x_2921_, v_keys_2917_, v___x_2919_);
v___x_2923_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(v_d_2916_, v_k_2922_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v___x_2924_; 
v___x_2924_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
return v___x_2924_;
}
else
{
lean_object* v_val_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_val_2925_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_val_2925_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2926_ = lean_unsigned_to_nat(1u);
v___x_2927_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(v_keys_2917_, v___x_2926_, v_val_2925_);
return v___x_2927_;
}
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = lean_obj_once(&l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1, &l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1);
v___x_2929_ = l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1___redArg(v___x_2928_);
return v___x_2929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___boxed(lean_object* v_d_2930_, lean_object* v_keys_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg(v_d_2930_, v_keys_2931_);
lean_dec_ref(v_keys_2931_);
lean_dec_ref(v_d_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys(lean_object* v_00_u03b1_2933_, lean_object* v_d_2934_, lean_object* v_keys_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg(v_d_2934_, v_keys_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___boxed(lean_object* v_00_u03b1_2937_, lean_object* v_d_2938_, lean_object* v_keys_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_Meta_DiscrTree_getEntriesWithKeys(v_00_u03b1_2937_, v_d_2938_, v_keys_2939_);
lean_dec_ref(v_keys_2939_);
lean_dec_ref(v_d_2938_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0(lean_object* v_00_u03b2_2941_, lean_object* v_x_2942_, lean_object* v_x_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(v_x_2942_, v_x_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___boxed(lean_object* v_00_u03b2_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0(v_00_u03b2_2945_, v_x_2946_, v_x_2947_);
lean_dec(v_x_2947_);
lean_dec_ref(v_x_2946_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0(lean_object* v_00_u03b2_2949_, lean_object* v_x_2950_, size_t v_x_2951_, lean_object* v_x_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(v_x_2950_, v_x_2951_, v_x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2954_, lean_object* v_x_2955_, lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
size_t v_x_349__boxed_2958_; lean_object* v_res_2959_; 
v_x_349__boxed_2958_ = lean_unbox_usize(v_x_2956_);
lean_dec(v_x_2956_);
v_res_2959_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0(v_00_u03b2_2954_, v_x_2955_, v_x_349__boxed_2958_, v_x_2957_);
lean_dec(v_x_2957_);
lean_dec_ref(v_x_2955_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2960_, lean_object* v_keys_2961_, lean_object* v_vals_2962_, lean_object* v_heq_2963_, lean_object* v_i_2964_, lean_object* v_k_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(v_keys_2961_, v_vals_2962_, v_i_2964_, v_k_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2967_, lean_object* v_keys_2968_, lean_object* v_vals_2969_, lean_object* v_heq_2970_, lean_object* v_i_2971_, lean_object* v_k_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2(v_00_u03b2_2967_, v_keys_2968_, v_vals_2969_, v_heq_2970_, v_i_2971_, v_k_2972_);
lean_dec(v_k_2972_);
lean_dec_ref(v_vals_2969_);
lean_dec_ref(v_keys_2968_);
return v_res_2973_;
}
}
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_DiscrTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DiscrTree_instToExprKey = _init_l_Lean_Meta_DiscrTree_instToExprKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instToExprKey);
l_Lean_Meta_DiscrTree_instLTKey = _init_l_Lean_Meta_DiscrTree_instLTKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instLTKey);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_DiscrTree_Types(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_DiscrTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_DiscrTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_DiscrTree_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
