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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_779_, lean_object* v_declHint_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_env_785_; uint8_t v___x_786_; 
v___x_783_ = lean_box(0);
v___x_784_ = lean_st_ref_get(v___y_781_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_env_785_);
lean_dec(v___x_784_);
v___x_786_ = l_Lean_Name_isAnonymous(v_declHint_780_);
if (v___x_786_ == 0)
{
uint8_t v_isExporting_787_; 
v_isExporting_787_ = lean_ctor_get_uint8(v_env_785_, sizeof(void*)*13);
if (v_isExporting_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec_ref(v_env_785_);
lean_dec(v_declHint_780_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_msg_779_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
lean_inc_ref(v_env_785_);
v___x_789_ = l_Lean_Environment_setExporting(v_env_785_, v___x_786_);
lean_inc(v_declHint_780_);
lean_inc_ref(v___x_789_);
v___x_790_ = l_Lean_Environment_contains(v___x_789_, v_declHint_780_, v_isExporting_787_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec_ref(v___x_789_);
lean_dec_ref(v_env_785_);
lean_dec(v_declHint_780_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_msg_779_);
return v___x_791_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_c_797_; lean_object* v___x_798_; 
v___x_792_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1);
v___x_793_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4);
v___x_794_ = l_Lean_Options_empty;
lean_inc_ref(v___x_789_);
v___x_795_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_795_, 0, v___x_789_);
lean_ctor_set(v___x_795_, 1, v___x_792_);
lean_ctor_set(v___x_795_, 2, v___x_793_);
lean_ctor_set(v___x_795_, 3, v___x_794_);
lean_inc(v_declHint_780_);
v___x_796_ = l_Lean_MessageData_ofConstName(v_declHint_780_, v___x_786_);
v_c_797_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_797_, 0, v___x_795_);
lean_ctor_set(v_c_797_, 1, v___x_796_);
v___x_798_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_789_, v_declHint_780_);
lean_dec_ref(v___x_789_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v_env_785_);
lean_dec(v_declHint_780_);
v___x_799_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v_c_797_);
v___x_801_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Lean_MessageData_note(v___x_802_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v_msg_779_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
else
{
lean_object* v_val_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_840_; 
v_val_806_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_840_ == 0)
{
v___x_808_ = v___x_798_;
v_isShared_809_ = v_isSharedCheck_840_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_val_806_);
lean_dec(v___x_798_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_840_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v_moduleNames_811_; lean_object* v_mod_812_; uint8_t v___x_813_; 
v___x_810_ = l_Lean_Environment_header(v_env_785_);
lean_dec_ref(v_env_785_);
v_moduleNames_811_ = lean_ctor_get(v___x_810_, 4);
lean_inc_ref(v_moduleNames_811_);
lean_dec_ref(v___x_810_);
v_mod_812_ = lean_array_get(v___x_783_, v_moduleNames_811_, v_val_806_);
lean_dec(v_val_806_);
lean_dec_ref(v_moduleNames_811_);
v___x_813_ = l_Lean_isPrivateName(v_declHint_780_);
lean_dec(v_declHint_780_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v_c_797_);
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_MessageData_ofName(v_mod_812_);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = l_Lean_MessageData_note(v___x_821_);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v_msg_779_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
lean_ctor_set(v___x_808_, 0, v___x_823_);
v___x_825_ = v___x_808_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_c_797_);
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_MessageData_ofName(v_mod_812_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = l_Lean_MessageData_note(v___x_834_);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v_msg_779_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
lean_ctor_set(v___x_808_, 0, v___x_836_);
v___x_838_ = v___x_808_;
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
lean_object* v___x_841_; 
lean_dec_ref(v_env_785_);
lean_dec(v_declHint_780_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v_msg_779_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_842_, lean_object* v_declHint_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_842_, v_declHint_843_, v___y_844_);
lean_dec(v___y_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_847_, lean_object* v_declHint_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_863_; 
v___x_853_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_847_, v_declHint_848_, v___y_851_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_863_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_863_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_863_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_858_ = l_Lean_unknownIdentifierMessageTag;
v___x_859_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v_a_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_859_);
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_864_, lean_object* v_declHint_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_864_, v_declHint_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_871_, lean_object* v_msg_872_, lean_object* v_declHint_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; lean_object* v_a_879_; lean_object* v___x_880_; 
v___x_878_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_872_, v_declHint_873_, v___y_874_, v___y_875_, v___y_876_);
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref(v___x_878_);
v___x_880_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_871_, v_a_879_, v___y_874_, v___y_875_, v___y_876_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_881_, lean_object* v_msg_882_, lean_object* v_declHint_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_881_, v_msg_882_, v_declHint_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec(v_ref_881_);
return v_res_888_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_895_, lean_object* v_constName_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_901_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
v___x_902_ = 0;
lean_inc(v_constName_896_);
v___x_903_ = l_Lean_MessageData_ofConstName(v_constName_896_, v___x_902_);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_901_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_895_, v___x_906_, v_constName_896_, v___y_897_, v___y_898_, v___y_899_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_908_, lean_object* v_constName_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_908_, v_constName_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec(v_ref_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_ref_920_; lean_object* v___x_921_; 
v_ref_920_ = lean_ctor_get(v___y_917_, 2);
v___x_921_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_920_, v_constName_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(lean_object* v_constName_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; lean_object* v_env_934_; uint8_t v___x_935_; lean_object* v___x_936_; 
v___x_933_ = lean_st_ref_get(v___y_931_);
v_env_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc_ref(v_env_934_);
lean_dec(v___x_933_);
v___x_935_ = 0;
lean_inc(v_constName_928_);
v___x_936_ = l_Lean_Environment_findConstVal_x3f(v_env_934_, v_constName_928_, v___x_935_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_937_;
}
else
{
lean_object* v_val_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_constName_928_);
v_val_938_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_936_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_val_938_);
lean_dec(v___x_936_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 0);
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_val_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0___boxed(lean_object* v_constName_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
if (lean_obj_tag(v_a_952_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = l_List_reverse___redArg(v_a_953_);
return v___x_954_;
}
else
{
lean_object* v_head_955_; lean_object* v_tail_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v_head_955_ = lean_ctor_get(v_a_952_, 0);
v_tail_956_ = lean_ctor_get(v_a_952_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v_a_952_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_tail_956_);
lean_inc(v_head_955_);
lean_dec(v_a_952_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = l_Lean_mkLevelParam(v_head_955_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v_a_953_);
lean_ctor_set(v___x_958_, 0, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_a_953_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v_a_952_ = v_tail_956_;
v_a_953_ = v___x_962_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(lean_object* v_constName_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
lean_inc(v_constName_966_);
v___x_971_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_983_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_983_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_983_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_983_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_levelParams_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v_levelParams_976_ = lean_ctor_get(v_a_972_, 1);
lean_inc(v_levelParams_976_);
lean_dec(v_a_972_);
v___x_977_ = lean_box(0);
v___x_978_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(v_levelParams_976_, v___x_977_);
v___x_979_ = l_Lean_mkConst(v_constName_966_, v___x_978_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_979_);
v___x_981_ = v___x_974_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_constName_966_);
v_a_984_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_971_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_971_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0___boxed(lean_object* v_constName_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_constName_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
return v_res_997_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1));
v___x_1004_ = l_Lean_MessageData_ofFormat(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4));
v___x_1009_ = l_Lean_MessageData_ofFormat(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__6));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(uint8_t v_parenIfNonAtomic_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_1016_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1139_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1139_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1139_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
if (lean_obj_tag(v_a_1021_) == 1)
{
lean_object* v_val_1025_; 
v_val_1025_ = lean_ctor_get(v_a_1021_, 0);
lean_inc(v_val_1025_);
lean_dec_ref_known(v_a_1021_, 1);
switch(lean_obj_tag(v_val_1025_))
{
case 0:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1026_);
v___x_1028_ = v___x_1023_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
case 1:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1030_);
v___x_1032_ = v___x_1023_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
case 2:
{
lean_object* v_a_1034_; 
v_a_1034_ = lean_ctor_get(v_val_1025_, 0);
lean_inc_ref(v_a_1034_);
lean_dec_ref_known(v_val_1025_, 1);
if (lean_obj_tag(v_a_1034_) == 0)
{
lean_object* v_val_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1047_; 
v_val_1035_ = lean_ctor_get(v_a_1034_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1037_ = v_a_1034_;
v_isShared_1038_ = v_isSharedCheck_1047_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_val_1035_);
lean_dec(v_a_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1047_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = l_Nat_reprFast(v_val_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 3);
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = l_Lean_MessageData_ofFormat(v___x_1041_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1042_);
v___x_1044_ = v___x_1023_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_val_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v_val_1048_ = lean_ctor_get(v_a_1034_, 0);
lean_inc_ref(v_val_1048_);
lean_dec_ref_known(v_a_1034_, 1);
v___x_1049_ = l_Lean_stringToMessageData(v_val_1048_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1049_);
v___x_1051_ = v___x_1023_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
case 3:
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1055_; 
lean_del_object(v___x_1023_);
v_a_1053_ = lean_ctor_get(v_val_1025_, 0);
lean_inc(v_a_1053_);
v_a_1054_ = lean_ctor_get(v_val_1025_, 1);
lean_inc(v_a_1054_);
lean_dec_ref_known(v_val_1025_, 2);
v___x_1055_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_1054_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1055_, 1);
v___x_1057_ = l_Lean_mkFVar(v_a_1053_);
v___x_1058_ = l_Lean_MessageData_ofExpr(v___x_1057_);
v___x_1059_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_1058_, v_a_1056_, v_parenIfNonAtomic_1015_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1056_);
return v___x_1059_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v_a_1053_);
v_a_1060_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1055_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1055_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
case 4:
{
lean_object* v_a_1068_; lean_object* v_a_1069_; lean_object* v___x_1070_; 
lean_del_object(v___x_1023_);
v_a_1068_ = lean_ctor_get(v_val_1025_, 0);
lean_inc(v_a_1068_);
v_a_1069_ = lean_ctor_get(v_val_1025_, 1);
lean_inc(v_a_1069_);
lean_dec_ref_known(v_val_1025_, 2);
v___x_1070_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_a_1068_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_1069_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1069_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = l_Lean_MessageData_ofExpr(v_a_1071_);
v___x_1075_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_1074_, v_a_1073_, v_parenIfNonAtomic_1015_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1073_);
return v___x_1075_;
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_a_1071_);
v_a_1076_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1072_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1072_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_a_1069_);
v_a_1084_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1070_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1070_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
case 5:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_del_object(v___x_1023_);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v___x_1092_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7);
v___x_1096_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_1095_, v_a_1094_, v_parenIfNonAtomic_1015_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1094_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1093_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1093_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
default: 
{
lean_object* v_a_1105_; lean_object* v_a_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; 
lean_del_object(v___x_1023_);
v_a_1105_ = lean_ctor_get(v_val_1025_, 1);
lean_inc(v_a_1105_);
v_a_1106_ = lean_ctor_get(v_val_1025_, 2);
lean_inc(v_a_1106_);
lean_dec_ref_known(v_val_1025_, 3);
v___x_1107_ = 1;
v___x_1108_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1107_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1134_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1134_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1134_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; 
v___x_1113_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_1106_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1106_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_a_1109_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_a_1105_, v___x_1117_);
lean_dec(v_a_1105_);
v___x_1119_ = l_Nat_reprFast(v___x_1118_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 3);
lean_ctor_set(v___x_1111_, 0, v___x_1119_);
v___x_1121_ = v___x_1111_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = l_Lean_MessageData_ofFormat(v___x_1121_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1116_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_1123_, v_a_1114_, v_parenIfNonAtomic_1015_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1114_);
return v___x_1124_;
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_del_object(v___x_1111_);
lean_dec(v_a_1109_);
lean_dec(v_a_1105_);
v_a_1126_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1113_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1113_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
else
{
lean_dec(v_a_1106_);
lean_dec(v_a_1105_);
return v___x_1108_;
}
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
lean_dec(v_a_1021_);
v___x_1135_ = l_Lean_MessageData_nil;
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1135_);
v___x_1137_ = v___x_1023_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_a_1140_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1020_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1020_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(lean_object* v_upperBound_1148_, lean_object* v_a_1149_, lean_object* v_b_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_nat_dec_lt(v_a_1149_, v_upperBound_1148_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec(v_a_1149_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_b_1150_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1155_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = lean_array_push(v_b_1150_, v_a_1158_);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_a_1149_, v___x_1160_);
lean_dec(v_a_1149_);
v_a_1149_ = v___x_1161_;
v_b_1150_ = v___x_1159_;
goto _start;
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v_b_1150_);
lean_dec(v_a_1149_);
v_a_1163_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1157_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1157_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(lean_object* v_num_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v_r_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_unsigned_to_nat(0u);
v_r_1177_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0));
v___x_1178_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_num_1171_, v___x_1176_, v_r_1177_, v_a_1172_, v_a_1173_, v_a_1174_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___boxed(lean_object* v_num_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_num_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec(v_num_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg___boxed(lean_object* v_upperBound_1185_, lean_object* v_a_1186_, lean_object* v_b_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_1185_, v_a_1186_, v_b_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v_upperBound_1185_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___boxed(lean_object* v_parenIfNonAtomic_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
uint8_t v_parenIfNonAtomic_boxed_1198_; lean_object* v_res_1199_; 
v_parenIfNonAtomic_boxed_1198_ = lean_unbox(v_parenIfNonAtomic_1193_);
v_res_1199_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v_parenIfNonAtomic_boxed_1198_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(lean_object* v_upperBound_1200_, lean_object* v_inst_1201_, lean_object* v_R_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_, lean_object* v_c_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_1200_, v_a_1203_, v_b_1204_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___boxed(lean_object* v_upperBound_1211_, lean_object* v_inst_1212_, lean_object* v_R_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_, lean_object* v_c_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(v_upperBound_1211_, v_inst_1212_, v_R_1213_, v_a_1214_, v_b_1215_, v_c_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec(v_upperBound_1211_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1222_, lean_object* v_constName_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_constName_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(v_00_u03b1_1229_, v_constName_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_1236_, lean_object* v_ref_1237_, lean_object* v_constName_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1237_, v_constName_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_ref_1245_, lean_object* v_constName_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_1244_, v_ref_1245_, v_constName_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v_ref_1245_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1252_, lean_object* v_ref_1253_, lean_object* v_msg_1254_, lean_object* v_declHint_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1253_, v_msg_1254_, v_declHint_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_ref_1262_, lean_object* v_msg_1263_, lean_object* v_declHint_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_1261_, v_ref_1262_, v_msg_1263_, v_declHint_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec(v_ref_1262_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_1270_, lean_object* v_declHint_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1270_, v_declHint_1271_, v___y_1274_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_1277_, lean_object* v_declHint_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_1277_, v_declHint_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1284_, lean_object* v_ref_1285_, lean_object* v_msg_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_1285_, v_msg_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_ref_1293_, lean_object* v_msg_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1292_, v_ref_1293_, v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec(v_ref_1293_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_1300_, lean_object* v_msg_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1301_, v___y_1303_, v___y_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_msg_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_1307_, v_msg_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern(lean_object* v_keys_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = 0;
v___x_1319_ = lean_array_to_list(v_keys_1314_);
v___x_1320_ = lean_st_mk_ref(v___x_1319_);
v___x_1321_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1318_, v___x_1320_, v_a_1315_, v_a_1316_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1330_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_st_ref_get(v___x_1320_);
lean_dec(v___x_1320_);
lean_dec(v___x_1326_);
if (v_isShared_1325_ == 0)
{
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1322_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_dec(v___x_1320_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern___boxed(lean_object* v_keys_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1331_, v_a_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object* v_keys_1336_, lean_object* v_v_1337_, lean_object* v_i_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1339_, 0, v_keys_1336_);
lean_ctor_set(v___x_1339_, 1, v_i_1338_);
lean_ctor_set(v___x_1339_, 2, v_v_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object* v_00_u03b1_1340_, lean_object* v_keys_1341_, lean_object* v_v_1342_, lean_object* v_i_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1344_, 0, v_keys_1341_);
lean_ctor_set(v___x_1344_, 1, v_i_1343_);
lean_ctor_set(v___x_1344_, 2, v_v_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(lean_object* v_inst_1345_, lean_object* v_vs_1346_, lean_object* v_v_1347_, lean_object* v_i_1348_){
_start:
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = lean_array_get_size(v_vs_1346_);
v___x_1350_ = lean_nat_dec_lt(v_i_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec(v_i_1348_);
lean_dec_ref(v_inst_1345_);
v___x_1351_ = lean_array_push(v_vs_1346_, v_v_1347_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1352_ = lean_array_fget_borrowed(v_vs_1346_, v_i_1348_);
lean_inc_ref(v_inst_1345_);
lean_inc(v___x_1352_);
lean_inc(v_v_1347_);
v___x_1353_ = lean_apply_2(v_inst_1345_, v_v_1347_, v___x_1352_);
v___x_1354_ = lean_unbox(v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = lean_nat_add(v_i_1348_, v___x_1355_);
lean_dec(v_i_1348_);
v_i_1348_ = v___x_1356_;
goto _start;
}
else
{
lean_object* v___x_1358_; 
lean_dec_ref(v_inst_1345_);
v___x_1358_ = lean_array_fset(v_vs_1346_, v_i_1348_, v_v_1347_);
lean_dec(v_i_1348_);
return v___x_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop(lean_object* v_00_u03b1_1359_, lean_object* v_inst_1360_, lean_object* v_vs_1361_, lean_object* v_v_1362_, lean_object* v_i_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(v_inst_1360_, v_vs_1361_, v_v_1362_, v_i_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(lean_object* v_inst_1365_, lean_object* v_vs_1366_, lean_object* v_v_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(v_inst_1365_, v_vs_1366_, v_v_1367_, v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal(lean_object* v_00_u03b1_1370_, lean_object* v_inst_1371_, lean_object* v_vs_1372_, lean_object* v_v_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_1371_, v_vs_1372_, v_v_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(lean_object* v_a_1375_, lean_object* v_b_1376_){
_start:
{
lean_object* v_fst_1377_; lean_object* v_fst_1378_; uint8_t v___x_1379_; 
v_fst_1377_ = lean_ctor_get(v_a_1375_, 0);
v_fst_1378_ = lean_ctor_get(v_b_1376_, 0);
v___x_1379_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1377_, v_fst_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed(lean_object* v_a_1380_, lean_object* v_b_1381_){
_start:
{
uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_res_1382_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(v_a_1380_, v_b_1381_);
lean_dec_ref(v_b_1381_);
lean_dec_ref(v_a_1380_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(lean_object* v___x_1384_, lean_object* v_x_1385_){
_start:
{
lean_inc_ref(v___x_1384_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed(lean_object* v___x_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(v___x_1386_, v_x_1387_);
lean_dec_ref(v_x_1387_);
lean_dec_ref(v___x_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(lean_object* v___x_1389_, lean_object* v_x_1390_){
_start:
{
lean_inc_ref(v___x_1389_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed(lean_object* v___x_1391_, lean_object* v_x_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(v___x_1391_, v_x_1392_);
lean_dec_ref(v___x_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4(lean_object* v_i_1394_, lean_object* v_keys_1395_, lean_object* v_v_1396_, lean_object* v_k_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_c_1401_; lean_object* v___x_1402_; 
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = lean_nat_add(v_i_1394_, v___x_1399_);
v_c_1401_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_c_1401_, 0, v_keys_1395_);
lean_ctor_set(v_c_1401_, 1, v___x_1400_);
lean_ctor_set(v_c_1401_, 2, v_v_1396_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_k_1397_);
lean_ctor_set(v___x_1402_, 1, v_c_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4___boxed(lean_object* v_i_1403_, lean_object* v_keys_1404_, lean_object* v_v_1405_, lean_object* v_k_1406_, lean_object* v_x_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4(v_i_1403_, v_keys_1404_, v_v_1405_, v_k_1406_, v_x_1407_);
lean_dec(v_i_1403_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3___boxed(lean_object* v_i_1429_, lean_object* v_inst_1430_, lean_object* v_keys_1431_, lean_object* v_v_1432_, lean_object* v_k_1433_, lean_object* v_x_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3(v_i_1429_, v_inst_1430_, v_keys_1431_, v_v_1432_, v_k_1433_, v_x_1434_);
lean_dec(v_i_1429_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(lean_object* v_inst_1436_, lean_object* v_keys_1437_, lean_object* v_v_1438_, lean_object* v_i_1439_, lean_object* v_t_1440_){
_start:
{
lean_object* v___f_1441_; lean_object* v___x_1442_; lean_object* v_val_1444_; 
v___f_1441_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0));
v___x_1442_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
switch(lean_obj_tag(v_t_1440_))
{
case 2:
{
lean_object* v___x_1504_; 
v___x_1504_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_1440_);
v_val_1444_ = v___x_1504_;
goto v___jp_1443_;
}
case 3:
{
lean_object* v___x_1505_; 
v___x_1505_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_1440_);
v_val_1444_ = v___x_1505_;
goto v___jp_1443_;
}
default: 
{
v_val_1444_ = v_t_1440_;
goto v___jp_1443_;
}
}
v___jp_1443_:
{
if (lean_obj_tag(v_val_1444_) == 0)
{
lean_object* v_key_1445_; lean_object* v_child_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1482_; 
v_key_1445_ = lean_ctor_get(v_val_1444_, 0);
v_child_1446_ = lean_ctor_get(v_val_1444_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_val_1444_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1448_ = v_val_1444_;
v_isShared_1449_ = v_isSharedCheck_1482_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_child_1446_);
lean_inc(v_key_1445_);
lean_dec(v_val_1444_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1482_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1450_ = lean_array_get_size(v_keys_1437_);
v___x_1451_ = lean_nat_dec_lt(v_i_1439_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec(v_i_1439_);
lean_dec_ref(v_keys_1437_);
lean_dec_ref(v_inst_1436_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_mk_empty_array_with_capacity(v___x_1452_);
lean_inc_ref(v___x_1453_);
v___x_1454_ = lean_array_push(v___x_1453_, v_v_1438_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_key_1445_);
lean_ctor_set(v___x_1455_, 1, v_child_1446_);
v___x_1456_ = lean_array_push(v___x_1453_, v___x_1455_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 1);
lean_ctor_set(v___x_1448_, 1, v___x_1456_);
lean_ctor_set(v___x_1448_, 0, v___x_1454_);
v___x_1458_ = v___x_1448_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1460_ = lean_array_fget_borrowed(v_keys_1437_, v_i_1439_);
v___x_1461_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_1460_, v_key_1445_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___f_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_inc(v___x_1460_);
lean_dec_ref(v_inst_1436_);
v___x_1462_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_key_1445_);
lean_ctor_set(v___x_1463_, 1, v_child_1446_);
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_mk_empty_array_with_capacity(v___x_1464_);
v___x_1466_ = lean_array_push(v___x_1465_, v___x_1463_);
v___x_1467_ = lean_nat_add(v_i_1439_, v___x_1464_);
lean_dec(v_i_1439_);
v___x_1468_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1468_, 0, v_keys_1437_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
lean_ctor_set(v___x_1468_, 2, v_v_1438_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1460_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
lean_inc_ref_n(v___x_1469_, 2);
v___f_1470_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1470_, 0, v___x_1469_);
v___f_1471_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1471_, 0, v___x_1469_);
v___x_1472_ = l_Array_binInsertM___redArg(v___x_1442_, v___f_1441_, v___f_1470_, v___f_1471_, v___x_1466_, v___x_1469_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 1);
lean_ctor_set(v___x_1448_, 1, v___x_1472_);
lean_ctor_set(v___x_1448_, 0, v___x_1462_);
v___x_1474_ = v___x_1448_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = lean_nat_add(v_i_1439_, v___x_1476_);
lean_dec(v_i_1439_);
v___x_1478_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1436_, v_keys_1437_, v_v_1438_, v___x_1477_, v_child_1446_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v___x_1478_);
v___x_1480_ = v___x_1448_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_key_1445_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_object* v_vs_1483_; lean_object* v_children_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1503_; 
v_vs_1483_ = lean_ctor_get(v_val_1444_, 0);
v_children_1484_ = lean_ctor_get(v_val_1444_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_val_1444_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1486_ = v_val_1444_;
v_isShared_1487_ = v_isSharedCheck_1503_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_children_1484_);
lean_inc(v_vs_1483_);
lean_dec(v_val_1444_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1503_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_array_get_size(v_keys_1437_);
v___x_1489_ = lean_nat_dec_lt(v_i_1439_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_dec(v_i_1439_);
lean_dec_ref(v_keys_1437_);
v___x_1490_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_1436_, v_vs_1483_, v_v_1438_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1490_);
v___x_1492_ = v___x_1486_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_children_1484_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v_k_1494_; lean_object* v___f_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_c_1499_; lean_object* v___x_1501_; 
v_k_1494_ = lean_array_fget(v_keys_1437_, v_i_1439_);
lean_inc_n(v_k_1494_, 2);
lean_inc(v_v_1438_);
lean_inc_ref(v_keys_1437_);
lean_inc(v_i_1439_);
v___f_1495_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_1495_, 0, v_i_1439_);
lean_closure_set(v___f_1495_, 1, v_inst_1436_);
lean_closure_set(v___f_1495_, 2, v_keys_1437_);
lean_closure_set(v___f_1495_, 3, v_v_1438_);
lean_closure_set(v___f_1495_, 4, v_k_1494_);
v___f_1496_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_1496_, 0, v_i_1439_);
lean_closure_set(v___f_1496_, 1, v_keys_1437_);
lean_closure_set(v___f_1496_, 2, v_v_1438_);
lean_closure_set(v___f_1496_, 3, v_k_1494_);
v___x_1497_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1));
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_k_1494_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v_c_1499_ = l_Array_binInsertM___redArg(v___x_1442_, v___f_1441_, v___f_1495_, v___f_1496_, v_children_1484_, v___x_1498_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v_c_1499_);
v___x_1501_ = v___x_1486_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_vs_1483_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_c_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__3(lean_object* v_i_1506_, lean_object* v_inst_1507_, lean_object* v_keys_1508_, lean_object* v_v_1509_, lean_object* v_k_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1522_; 
v_snd_1512_ = lean_ctor_get(v_x_1511_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_x_1511_, 0);
lean_dec(v_unused_1523_);
v___x_1514_ = v_x_1511_;
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_dec(v_x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v_c_1518_; lean_object* v___x_1520_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_i_1506_, v___x_1516_);
v_c_1518_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1507_, v_keys_1508_, v_v_1509_, v___x_1517_, v_snd_1512_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_c_1518_);
lean_ctor_set(v___x_1514_, 0, v_k_1510_);
v___x_1520_ = v___x_1514_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_k_1510_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_c_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux(lean_object* v_00_u03b1_1524_, lean_object* v_inst_1525_, lean_object* v_keys_1526_, lean_object* v_v_1527_, lean_object* v_i_1528_, lean_object* v_t_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1525_, v_keys_1526_, v_v_1527_, v_i_1528_, v_t_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux_match__1_splitter___redArg(lean_object* v_x_1531_, lean_object* v_h__1_1532_, lean_object* v_h__2_1533_){
_start:
{
if (lean_obj_tag(v_x_1531_) == 0)
{
lean_object* v_key_1534_; lean_object* v_child_1535_; lean_object* v___x_1536_; 
lean_dec(v_h__2_1533_);
v_key_1534_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_key_1534_);
v_child_1535_ = lean_ctor_get(v_x_1531_, 1);
lean_inc_ref(v_child_1535_);
lean_dec_ref_known(v_x_1531_, 2);
v___x_1536_ = lean_apply_3(v_h__1_1532_, v_key_1534_, v_child_1535_, lean_box(0));
return v___x_1536_;
}
else
{
lean_object* v_vs_1537_; lean_object* v_children_1538_; lean_object* v___x_1539_; 
lean_dec(v_h__1_1532_);
v_vs_1537_ = lean_ctor_get(v_x_1531_, 0);
lean_inc_ref(v_vs_1537_);
v_children_1538_ = lean_ctor_get(v_x_1531_, 1);
lean_inc_ref(v_children_1538_);
lean_dec_ref_known(v_x_1531_, 2);
v___x_1539_ = lean_apply_3(v_h__2_1533_, v_vs_1537_, v_children_1538_, lean_box(0));
return v___x_1539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux_match__1_splitter(lean_object* v_00_u03b1_1540_, lean_object* v_motive_1541_, lean_object* v_x_1542_, lean_object* v_h__1_1543_, lean_object* v_h__2_1544_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 0)
{
lean_object* v_key_1545_; lean_object* v_child_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__2_1544_);
v_key_1545_ = lean_ctor_get(v_x_1542_, 0);
lean_inc(v_key_1545_);
v_child_1546_ = lean_ctor_get(v_x_1542_, 1);
lean_inc_ref(v_child_1546_);
lean_dec_ref_known(v_x_1542_, 2);
v___x_1547_ = lean_apply_3(v_h__1_1543_, v_key_1545_, v_child_1546_, lean_box(0));
return v___x_1547_;
}
else
{
lean_object* v_vs_1548_; lean_object* v_children_1549_; lean_object* v___x_1550_; 
lean_dec(v_h__1_1543_);
v_vs_1548_ = lean_ctor_get(v_x_1542_, 0);
lean_inc_ref(v_vs_1548_);
v_children_1549_ = lean_ctor_get(v_x_1542_, 1);
lean_inc_ref(v_children_1549_);
lean_dec_ref_known(v_x_1542_, 2);
v___x_1550_ = lean_apply_3(v_h__2_1544_, v_vs_1548_, v_children_1549_, lean_box(0));
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_format_match__1_splitter___redArg(lean_object* v_x_1551_, lean_object* v_h__1_1552_){
_start:
{
lean_object* v_fst_1553_; lean_object* v_snd_1554_; lean_object* v___x_1555_; 
v_fst_1553_ = lean_ctor_get(v_x_1551_, 0);
lean_inc(v_fst_1553_);
v_snd_1554_ = lean_ctor_get(v_x_1551_, 1);
lean_inc(v_snd_1554_);
lean_dec_ref(v_x_1551_);
v___x_1555_ = lean_apply_2(v_h__1_1552_, v_fst_1553_, v_snd_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_format_match__1_splitter(lean_object* v_00_u03b1_1556_, lean_object* v_motive_1557_, lean_object* v_x_1558_, lean_object* v_h__1_1559_){
_start:
{
lean_object* v_fst_1560_; lean_object* v_snd_1561_; lean_object* v___x_1562_; 
v_fst_1560_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_fst_1560_);
v_snd_1561_ = lean_ctor_get(v_x_1558_, 1);
lean_inc(v_snd_1561_);
lean_dec_ref(v_x_1558_);
v___x_1562_ = lean_apply_2(v_h__1_1559_, v_fst_1560_, v_snd_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___lam__0(lean_object* v_keys_1563_, lean_object* v_v_1564_, lean_object* v_inst_1565_, lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec_ref(v_inst_1565_);
v___x_1567_ = lean_unsigned_to_nat(1u);
v___x_1568_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1568_, 0, v_keys_1563_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_ctor_set(v___x_1568_, 2, v_v_1564_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
else
{
lean_object* v_val_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1579_; 
v_val_1570_ = lean_ctor_get(v_x_1566_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1572_ = v_x_1566_;
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_val_1570_);
lean_dec(v_x_1566_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1565_, v_keys_1563_, v_v_1564_, v___x_1574_, v_val_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1584_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3));
v___x_1585_ = lean_unsigned_to_nat(23u);
v___x_1586_ = lean_unsigned_to_nat(209u);
v___x_1587_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2));
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0));
v___x_1589_ = l_mkPanicMessageWithDecl(v___x_1588_, v___x_1587_, v___x_1586_, v___x_1585_, v___x_1584_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg(lean_object* v_inst_1590_, lean_object* v_d_1591_, lean_object* v_keys_1592_, lean_object* v_v_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1594_ = lean_array_get_size(v_keys_1592_);
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_nat_dec_eq(v___x_1594_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___f_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_k_1601_; uint64_t v___x_1602_; size_t v_h_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
lean_inc_ref(v_keys_1592_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1597_, 0, v_keys_1592_);
lean_closure_set(v___f_1597_, 1, v_v_1593_);
lean_closure_set(v___f_1597_, 2, v_inst_1590_);
v___x_1598_ = lean_box(0);
v___x_1599_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0));
v___x_1600_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1));
v_k_1601_ = lean_array_get(v___x_1598_, v_keys_1592_, v___x_1595_);
lean_dec_ref(v_keys_1592_);
v___x_1602_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1601_);
v_h_1603_ = lean_uint64_to_usize(v___x_1602_);
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = l_Lean_PersistentHashMap_alterAux___redArg(v___x_1599_, v___x_1600_, v___f_1597_, v_d_1591_, v_h_1603_, v___x_1604_, v_k_1601_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_v_1593_);
lean_dec_ref(v_keys_1592_);
lean_dec_ref(v_d_1591_);
lean_dec_ref(v_inst_1590_);
v___x_1606_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___closed__0, &l_Lean_Meta_DiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabited___closed__0);
v___x_1607_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4, &l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4);
v___x_1608_ = l_panic___redArg(v___x_1606_, v___x_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue(lean_object* v_00_u03b1_1609_, lean_object* v_inst_1610_, lean_object* v_d_1611_, lean_object* v_keys_1612_, lean_object* v_v_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_1610_, v_d_1611_, v_keys_1612_, v_v_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Array_instInhabited___redArg();
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg(lean_object* v_msg_1616_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0, &l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_panic_fn_borrowed(v___x_1618_, v_msg_1616_);
lean_dec_ref_known(v___x_1618_, 2);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0(lean_object* v_00_u03b1_1620_, lean_object* v_msg_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg(v_msg_1621_);
return v___x_1622_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__1));
v___x_1626_ = lean_unsigned_to_nat(15u);
v___x_1627_ = lean_unsigned_to_nat(238u);
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__0));
v___x_1629_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0));
v___x_1630_ = l_mkPanicMessageWithDecl(v___x_1629_, v___x_1628_, v___x_1627_, v___x_1626_, v___x_1625_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg(lean_object* v_x_1631_){
_start:
{
switch(lean_obj_tag(v_x_1631_))
{
case 0:
{
lean_object* v_key_1632_; lean_object* v_child_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_key_1632_ = lean_ctor_get(v_x_1631_, 0);
lean_inc(v_key_1632_);
v_child_1633_ = lean_ctor_get(v_x_1631_, 1);
lean_inc_ref(v_child_1633_);
lean_dec_ref_known(v_x_1631_, 2);
v___x_1634_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_key_1632_);
lean_ctor_set(v___x_1635_, 1, v_child_1633_);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_mk_empty_array_with_capacity(v___x_1636_);
v___x_1638_ = lean_array_push(v___x_1637_, v___x_1635_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1634_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
return v___x_1639_;
}
case 1:
{
lean_object* v_vs_1640_; lean_object* v_children_1641_; lean_object* v___x_1642_; 
v_vs_1640_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_vs_1640_);
v_children_1641_ = lean_ctor_get(v_x_1631_, 1);
lean_inc_ref(v_children_1641_);
lean_dec_ref_known(v_x_1631_, 2);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_vs_1640_);
lean_ctor_set(v___x_1642_, 1, v_children_1641_);
return v___x_1642_;
}
case 2:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec_ref_known(v_x_1631_, 1);
v___x_1643_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg___closed__2);
v___x_1644_ = l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg(v___x_1643_);
return v___x_1644_;
}
default: 
{
lean_object* v_keys_1645_; lean_object* v_i_1646_; lean_object* v_v_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1669_; 
v_keys_1645_ = lean_ctor_get(v_x_1631_, 0);
v_i_1646_ = lean_ctor_get(v_x_1631_, 1);
v_v_1647_ = lean_ctor_get(v_x_1631_, 2);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1649_ = v_x_1631_;
v_isShared_1650_ = v_isSharedCheck_1669_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_v_1647_);
lean_inc(v_i_1646_);
lean_inc(v_keys_1645_);
lean_dec(v_x_1631_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1669_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = lean_array_get_size(v_keys_1645_);
v___x_1652_ = lean_nat_dec_lt(v_i_1646_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_del_object(v___x_1649_);
lean_dec(v_i_1646_);
lean_dec_ref(v_keys_1645_);
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_mk_empty_array_with_capacity(v___x_1653_);
v___x_1655_ = lean_array_push(v___x_1654_, v_v_1647_);
v___x_1656_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfoldSuffix___redArg___closed__0));
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1658_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
v___x_1659_ = lean_array_fget(v_keys_1645_, v_i_1646_);
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_nat_add(v_i_1646_, v___x_1660_);
lean_dec(v_i_1646_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v___x_1661_);
v___x_1663_ = v___x_1649_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_keys_1645_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_v_1647_);
v___x_1663_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1659_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_mk_empty_array_with_capacity(v___x_1660_);
v___x_1666_ = lean_array_push(v___x_1665_, v___x_1664_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1658_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
return v___x_1667_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold(lean_object* v_00_u03b1_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold___redArg(v_x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_match__1_splitter___redArg(lean_object* v_x_1673_, lean_object* v_h__1_1674_, lean_object* v_h__2_1675_, lean_object* v_h__3_1676_, lean_object* v_h__4_1677_){
_start:
{
switch(lean_obj_tag(v_x_1673_))
{
case 0:
{
lean_object* v_key_1678_; lean_object* v_child_1679_; lean_object* v___x_1680_; 
lean_dec(v_h__4_1677_);
lean_dec(v_h__3_1676_);
lean_dec(v_h__2_1675_);
v_key_1678_ = lean_ctor_get(v_x_1673_, 0);
lean_inc(v_key_1678_);
v_child_1679_ = lean_ctor_get(v_x_1673_, 1);
lean_inc_ref(v_child_1679_);
lean_dec_ref_known(v_x_1673_, 2);
v___x_1680_ = lean_apply_2(v_h__1_1674_, v_key_1678_, v_child_1679_);
return v___x_1680_;
}
case 1:
{
lean_object* v_vs_1681_; lean_object* v_children_1682_; lean_object* v___x_1683_; 
lean_dec(v_h__4_1677_);
lean_dec(v_h__3_1676_);
lean_dec(v_h__1_1674_);
v_vs_1681_ = lean_ctor_get(v_x_1673_, 0);
lean_inc_ref(v_vs_1681_);
v_children_1682_ = lean_ctor_get(v_x_1673_, 1);
lean_inc_ref(v_children_1682_);
lean_dec_ref_known(v_x_1673_, 2);
v___x_1683_ = lean_apply_2(v_h__2_1675_, v_vs_1681_, v_children_1682_);
return v___x_1683_;
}
case 2:
{
lean_object* v_t_1684_; lean_object* v___x_1685_; 
lean_dec(v_h__3_1676_);
lean_dec(v_h__2_1675_);
lean_dec(v_h__1_1674_);
v_t_1684_ = lean_ctor_get(v_x_1673_, 0);
lean_inc_ref(v_t_1684_);
lean_dec_ref_known(v_x_1673_, 1);
v___x_1685_ = lean_apply_1(v_h__4_1677_, v_t_1684_);
return v___x_1685_;
}
default: 
{
lean_object* v_keys_1686_; lean_object* v_i_1687_; lean_object* v_v_1688_; lean_object* v___x_1689_; 
lean_dec(v_h__4_1677_);
lean_dec(v_h__2_1675_);
lean_dec(v_h__1_1674_);
v_keys_1686_ = lean_ctor_get(v_x_1673_, 0);
lean_inc_ref(v_keys_1686_);
v_i_1687_ = lean_ctor_get(v_x_1673_, 1);
lean_inc(v_i_1687_);
v_v_1688_ = lean_ctor_get(v_x_1673_, 2);
lean_inc(v_v_1688_);
lean_dec_ref_known(v_x_1673_, 3);
v___x_1689_ = lean_apply_3(v_h__3_1676_, v_keys_1686_, v_i_1687_, v_v_1688_);
return v___x_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_match__1_splitter(lean_object* v_00_u03b1_1690_, lean_object* v_motive_1691_, lean_object* v_x_1692_, lean_object* v_h__1_1693_, lean_object* v_h__2_1694_, lean_object* v_h__3_1695_, lean_object* v_h__4_1696_){
_start:
{
switch(lean_obj_tag(v_x_1692_))
{
case 0:
{
lean_object* v_key_1697_; lean_object* v_child_1698_; lean_object* v___x_1699_; 
lean_dec(v_h__4_1696_);
lean_dec(v_h__3_1695_);
lean_dec(v_h__2_1694_);
v_key_1697_ = lean_ctor_get(v_x_1692_, 0);
lean_inc(v_key_1697_);
v_child_1698_ = lean_ctor_get(v_x_1692_, 1);
lean_inc_ref(v_child_1698_);
lean_dec_ref_known(v_x_1692_, 2);
v___x_1699_ = lean_apply_2(v_h__1_1693_, v_key_1697_, v_child_1698_);
return v___x_1699_;
}
case 1:
{
lean_object* v_vs_1700_; lean_object* v_children_1701_; lean_object* v___x_1702_; 
lean_dec(v_h__4_1696_);
lean_dec(v_h__3_1695_);
lean_dec(v_h__1_1693_);
v_vs_1700_ = lean_ctor_get(v_x_1692_, 0);
lean_inc_ref(v_vs_1700_);
v_children_1701_ = lean_ctor_get(v_x_1692_, 1);
lean_inc_ref(v_children_1701_);
lean_dec_ref_known(v_x_1692_, 2);
v___x_1702_ = lean_apply_2(v_h__2_1694_, v_vs_1700_, v_children_1701_);
return v___x_1702_;
}
case 2:
{
lean_object* v_t_1703_; lean_object* v___x_1704_; 
lean_dec(v_h__3_1695_);
lean_dec(v_h__2_1694_);
lean_dec(v_h__1_1693_);
v_t_1703_ = lean_ctor_get(v_x_1692_, 0);
lean_inc_ref(v_t_1703_);
lean_dec_ref_known(v_x_1692_, 1);
v___x_1704_ = lean_apply_1(v_h__4_1696_, v_t_1703_);
return v___x_1704_;
}
default: 
{
lean_object* v_keys_1705_; lean_object* v_i_1706_; lean_object* v_v_1707_; lean_object* v___x_1708_; 
lean_dec(v_h__4_1696_);
lean_dec(v_h__2_1694_);
lean_dec(v_h__1_1693_);
v_keys_1705_ = lean_ctor_get(v_x_1692_, 0);
lean_inc_ref(v_keys_1705_);
v_i_1706_ = lean_ctor_get(v_x_1692_, 1);
lean_inc(v_i_1706_);
v_v_1707_ = lean_ctor_get(v_x_1692_, 2);
lean_inc(v_v_1707_);
lean_dec_ref_known(v_x_1692_, 3);
v___x_1708_ = lean_apply_3(v_h__3_1695_, v_keys_1705_, v_i_1706_, v_v_1707_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_match__1_splitter___redArg(lean_object* v_x_1709_, lean_object* v_h__1_1710_, lean_object* v_h__2_1711_, lean_object* v_h__3_1712_, lean_object* v_h__4_1713_){
_start:
{
switch(lean_obj_tag(v_x_1709_))
{
case 0:
{
lean_object* v_key_1714_; lean_object* v_child_1715_; lean_object* v___x_1716_; 
lean_dec(v_h__4_1713_);
lean_dec(v_h__3_1712_);
lean_dec(v_h__2_1711_);
v_key_1714_ = lean_ctor_get(v_x_1709_, 0);
lean_inc(v_key_1714_);
v_child_1715_ = lean_ctor_get(v_x_1709_, 1);
lean_inc_ref(v_child_1715_);
lean_dec_ref_known(v_x_1709_, 2);
v___x_1716_ = lean_apply_2(v_h__1_1710_, v_key_1714_, v_child_1715_);
return v___x_1716_;
}
case 1:
{
lean_object* v_vs_1717_; lean_object* v_children_1718_; lean_object* v_toList_1719_; lean_object* v___x_1720_; 
lean_dec(v_h__4_1713_);
lean_dec(v_h__3_1712_);
lean_dec(v_h__1_1710_);
v_vs_1717_ = lean_ctor_get(v_x_1709_, 0);
lean_inc_ref(v_vs_1717_);
v_children_1718_ = lean_ctor_get(v_x_1709_, 1);
lean_inc_ref(v_children_1718_);
lean_dec_ref_known(v_x_1709_, 2);
v_toList_1719_ = lean_array_to_list(v_children_1718_);
v___x_1720_ = lean_apply_2(v_h__2_1711_, v_vs_1717_, v_toList_1719_);
return v___x_1720_;
}
case 2:
{
lean_object* v_t_1721_; lean_object* v___x_1722_; 
lean_dec(v_h__4_1713_);
lean_dec(v_h__2_1711_);
lean_dec(v_h__1_1710_);
v_t_1721_ = lean_ctor_get(v_x_1709_, 0);
lean_inc_ref(v_t_1721_);
lean_dec_ref_known(v_x_1709_, 1);
v___x_1722_ = lean_apply_1(v_h__3_1712_, v_t_1721_);
return v___x_1722_;
}
default: 
{
lean_object* v_keys_1723_; lean_object* v_i_1724_; lean_object* v_v_1725_; lean_object* v___x_1726_; 
lean_dec(v_h__3_1712_);
lean_dec(v_h__2_1711_);
lean_dec(v_h__1_1710_);
v_keys_1723_ = lean_ctor_get(v_x_1709_, 0);
lean_inc_ref(v_keys_1723_);
v_i_1724_ = lean_ctor_get(v_x_1709_, 1);
lean_inc(v_i_1724_);
v_v_1725_ = lean_ctor_get(v_x_1709_, 2);
lean_inc(v_v_1725_);
lean_dec_ref_known(v_x_1709_, 3);
v___x_1726_ = lean_apply_3(v_h__4_1713_, v_keys_1723_, v_i_1724_, v_v_1725_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_match__1_splitter(lean_object* v_00_u03b1_1727_, lean_object* v_motive_1728_, lean_object* v_x_1729_, lean_object* v_h__1_1730_, lean_object* v_h__2_1731_, lean_object* v_h__3_1732_, lean_object* v_h__4_1733_){
_start:
{
switch(lean_obj_tag(v_x_1729_))
{
case 0:
{
lean_object* v_key_1734_; lean_object* v_child_1735_; lean_object* v___x_1736_; 
lean_dec(v_h__4_1733_);
lean_dec(v_h__3_1732_);
lean_dec(v_h__2_1731_);
v_key_1734_ = lean_ctor_get(v_x_1729_, 0);
lean_inc(v_key_1734_);
v_child_1735_ = lean_ctor_get(v_x_1729_, 1);
lean_inc_ref(v_child_1735_);
lean_dec_ref_known(v_x_1729_, 2);
v___x_1736_ = lean_apply_2(v_h__1_1730_, v_key_1734_, v_child_1735_);
return v___x_1736_;
}
case 1:
{
lean_object* v_vs_1737_; lean_object* v_children_1738_; lean_object* v_toList_1739_; lean_object* v___x_1740_; 
lean_dec(v_h__4_1733_);
lean_dec(v_h__3_1732_);
lean_dec(v_h__1_1730_);
v_vs_1737_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_vs_1737_);
v_children_1738_ = lean_ctor_get(v_x_1729_, 1);
lean_inc_ref(v_children_1738_);
lean_dec_ref_known(v_x_1729_, 2);
v_toList_1739_ = lean_array_to_list(v_children_1738_);
v___x_1740_ = lean_apply_2(v_h__2_1731_, v_vs_1737_, v_toList_1739_);
return v___x_1740_;
}
case 2:
{
lean_object* v_t_1741_; lean_object* v___x_1742_; 
lean_dec(v_h__4_1733_);
lean_dec(v_h__2_1731_);
lean_dec(v_h__1_1730_);
v_t_1741_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_t_1741_);
lean_dec_ref_known(v_x_1729_, 1);
v___x_1742_ = lean_apply_1(v_h__3_1732_, v_t_1741_);
return v___x_1742_;
}
default: 
{
lean_object* v_keys_1743_; lean_object* v_i_1744_; lean_object* v_v_1745_; lean_object* v___x_1746_; 
lean_dec(v_h__3_1732_);
lean_dec(v_h__2_1731_);
lean_dec(v_h__1_1730_);
v_keys_1743_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_keys_1743_);
v_i_1744_ = lean_ctor_get(v_x_1729_, 1);
lean_inc(v_i_1744_);
v_v_1745_ = lean_ctor_get(v_x_1729_, 2);
lean_inc(v_v_1745_);
lean_dec_ref_known(v_x_1729_, 3);
v___x_1746_ = lean_apply_3(v_h__4_1733_, v_keys_1743_, v_i_1744_, v_v_1745_);
return v___x_1746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_weights_match__1_splitter___redArg(lean_object* v_x_1747_, lean_object* v_h__1_1748_, lean_object* v_h__2_1749_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_h__2_1749_);
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_apply_1(v_h__1_1748_, v___x_1750_);
return v___x_1751_;
}
else
{
lean_object* v_head_1752_; lean_object* v_tail_1753_; lean_object* v_fst_1754_; lean_object* v_snd_1755_; lean_object* v___x_1756_; 
lean_dec(v_h__1_1748_);
v_head_1752_ = lean_ctor_get(v_x_1747_, 0);
lean_inc(v_head_1752_);
v_tail_1753_ = lean_ctor_get(v_x_1747_, 1);
lean_inc(v_tail_1753_);
lean_dec_ref_known(v_x_1747_, 2);
v_fst_1754_ = lean_ctor_get(v_head_1752_, 0);
lean_inc(v_fst_1754_);
v_snd_1755_ = lean_ctor_get(v_head_1752_, 1);
lean_inc(v_snd_1755_);
lean_dec(v_head_1752_);
v___x_1756_ = lean_apply_3(v_h__2_1749_, v_fst_1754_, v_snd_1755_, v_tail_1753_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_weight_weights_match__1_splitter(lean_object* v_00_u03b1_1757_, lean_object* v_motive_1758_, lean_object* v_x_1759_, lean_object* v_h__1_1760_, lean_object* v_h__2_1761_){
_start:
{
if (lean_obj_tag(v_x_1759_) == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_h__2_1761_);
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_apply_1(v_h__1_1760_, v___x_1762_);
return v___x_1763_;
}
else
{
lean_object* v_head_1764_; lean_object* v_tail_1765_; lean_object* v_fst_1766_; lean_object* v_snd_1767_; lean_object* v___x_1768_; 
lean_dec(v_h__1_1760_);
v_head_1764_ = lean_ctor_get(v_x_1759_, 0);
lean_inc(v_head_1764_);
v_tail_1765_ = lean_ctor_get(v_x_1759_, 1);
lean_inc(v_tail_1765_);
lean_dec_ref_known(v_x_1759_, 2);
v_fst_1766_ = lean_ctor_get(v_head_1764_, 0);
lean_inc(v_fst_1766_);
v_snd_1767_ = lean_ctor_get(v_head_1764_, 1);
lean_inc(v_snd_1767_);
lean_dec(v_head_1764_);
v___x_1768_ = lean_apply_3(v_h__2_1761_, v_fst_1766_, v_snd_1767_, v_tail_1765_);
return v___x_1768_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(lean_object* v_x1_1769_, lean_object* v_x2_1770_){
_start:
{
lean_object* v_snd_1771_; lean_object* v_snd_1772_; lean_object* v_snd_1773_; lean_object* v_snd_1774_; uint8_t v___x_1775_; 
v_snd_1771_ = lean_ctor_get(v_x1_1769_, 1);
v_snd_1772_ = lean_ctor_get(v_x2_1770_, 1);
v_snd_1773_ = lean_ctor_get(v_snd_1771_, 1);
v_snd_1774_ = lean_ctor_get(v_snd_1772_, 1);
v___x_1775_ = lean_nat_dec_lt(v_snd_1773_, v_snd_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0___boxed(lean_object* v_x1_1776_, lean_object* v_x2_1777_){
_start:
{
uint8_t v_res_1778_; lean_object* v_r_1779_; 
v_res_1778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(v_x1_1776_, v_x2_1777_);
lean_dec_ref(v_x2_1777_);
lean_dec_ref(v_x1_1776_);
v_r_1779_ = lean_box(v_res_1778_);
return v_r_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(lean_object* v_hi_1780_, lean_object* v_pivot_1781_, lean_object* v_as_1782_, lean_object* v_i_1783_, lean_object* v_k_1784_){
_start:
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_nat_dec_lt(v_k_1784_, v_hi_1780_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec(v_k_1784_);
v___x_1786_ = lean_array_fswap(v_as_1782_, v_i_1783_, v_hi_1780_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_i_1783_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
return v___x_1787_;
}
else
{
lean_object* v___x_1788_; lean_object* v_snd_1789_; lean_object* v_snd_1790_; lean_object* v_snd_1791_; lean_object* v_snd_1792_; uint8_t v___x_1793_; 
v___x_1788_ = lean_array_fget_borrowed(v_as_1782_, v_k_1784_);
v_snd_1789_ = lean_ctor_get(v___x_1788_, 1);
v_snd_1790_ = lean_ctor_get(v_pivot_1781_, 1);
v_snd_1791_ = lean_ctor_get(v_snd_1789_, 1);
v_snd_1792_ = lean_ctor_get(v_snd_1790_, 1);
v___x_1793_ = lean_nat_dec_lt(v_snd_1791_, v_snd_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_nat_add(v_k_1784_, v___x_1794_);
lean_dec(v_k_1784_);
v_k_1784_ = v___x_1795_;
goto _start;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1797_ = lean_array_fswap(v_as_1782_, v_i_1783_, v_k_1784_);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_add(v_i_1783_, v___x_1798_);
lean_dec(v_i_1783_);
v___x_1800_ = lean_nat_add(v_k_1784_, v___x_1798_);
lean_dec(v_k_1784_);
v_as_1782_ = v___x_1797_;
v_i_1783_ = v___x_1799_;
v_k_1784_ = v___x_1800_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg___boxed(lean_object* v_hi_1802_, lean_object* v_pivot_1803_, lean_object* v_as_1804_, lean_object* v_i_1805_, lean_object* v_k_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(v_hi_1802_, v_pivot_1803_, v_as_1804_, v_i_1805_, v_k_1806_);
lean_dec_ref(v_pivot_1803_);
lean_dec(v_hi_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(lean_object* v_n_1808_, lean_object* v_as_1809_, lean_object* v_lo_1810_, lean_object* v_hi_1811_){
_start:
{
lean_object* v___y_1813_; uint8_t v___x_1823_; 
v___x_1823_ = lean_nat_dec_lt(v_lo_1810_, v_hi_1811_);
if (v___x_1823_ == 0)
{
lean_dec(v_lo_1810_);
return v_as_1809_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_mid_1826_; lean_object* v___y_1828_; lean_object* v___y_1834_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1824_ = lean_nat_add(v_lo_1810_, v_hi_1811_);
v___x_1825_ = lean_unsigned_to_nat(1u);
v_mid_1826_ = lean_nat_shiftr(v___x_1824_, v___x_1825_);
lean_dec(v___x_1824_);
v___x_1839_ = lean_array_fget_borrowed(v_as_1809_, v_mid_1826_);
v___x_1840_ = lean_array_fget_borrowed(v_as_1809_, v_lo_1810_);
v___x_1841_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
v___y_1834_ = v_as_1809_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_array_fswap(v_as_1809_, v_lo_1810_, v_mid_1826_);
v___y_1834_ = v___x_1842_;
goto v___jp_1833_;
}
v___jp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1829_ = lean_array_fget_borrowed(v___y_1828_, v_mid_1826_);
v___x_1830_ = lean_array_fget_borrowed(v___y_1828_, v_hi_1811_);
v___x_1831_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(v___x_1829_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_dec(v_mid_1826_);
v___y_1813_ = v___y_1828_;
goto v___jp_1812_;
}
else
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_array_fswap(v___y_1828_, v_mid_1826_, v_hi_1811_);
lean_dec(v_mid_1826_);
v___y_1813_ = v___x_1832_;
goto v___jp_1812_;
}
}
v___jp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_array_fget_borrowed(v___y_1834_, v_hi_1811_);
v___x_1836_ = lean_array_fget_borrowed(v___y_1834_, v_lo_1810_);
v___x_1837_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___lam__0(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
v___y_1828_ = v___y_1834_;
goto v___jp_1827_;
}
else
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_array_fswap(v___y_1834_, v_lo_1810_, v_hi_1811_);
v___y_1828_ = v___x_1838_;
goto v___jp_1827_;
}
}
}
v___jp_1812_:
{
lean_object* v_pivot_1814_; lean_object* v___x_1815_; lean_object* v_fst_1816_; lean_object* v_snd_1817_; uint8_t v___x_1818_; 
v_pivot_1814_ = lean_array_fget(v___y_1813_, v_hi_1811_);
lean_inc_n(v_lo_1810_, 2);
v___x_1815_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(v_hi_1811_, v_pivot_1814_, v___y_1813_, v_lo_1810_, v_lo_1810_);
lean_dec(v_pivot_1814_);
v_fst_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_fst_1816_);
v_snd_1817_ = lean_ctor_get(v___x_1815_, 1);
lean_inc(v_snd_1817_);
lean_dec_ref(v___x_1815_);
v___x_1818_ = lean_nat_dec_le(v_hi_1811_, v_fst_1816_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(v_n_1808_, v_snd_1817_, v_lo_1810_, v_fst_1816_);
v___x_1820_ = lean_unsigned_to_nat(1u);
v___x_1821_ = lean_nat_add(v_fst_1816_, v___x_1820_);
lean_dec(v_fst_1816_);
v_as_1809_ = v___x_1819_;
v_lo_1810_ = v___x_1821_;
goto _start;
}
else
{
lean_dec(v_fst_1816_);
lean_dec(v_lo_1810_);
return v_snd_1817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg___boxed(lean_object* v_n_1843_, lean_object* v_as_1844_, lean_object* v_lo_1845_, lean_object* v_hi_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(v_n_1843_, v_as_1844_, v_lo_1845_, v_hi_1846_);
lean_dec(v_hi_1846_);
lean_dec(v_n_1843_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(lean_object* v_a_1848_, lean_object* v_b_1849_, lean_object* v_x_1850_){
_start:
{
if (lean_obj_tag(v_x_1850_) == 0)
{
lean_dec(v_b_1849_);
lean_dec(v_a_1848_);
return v_x_1850_;
}
else
{
lean_object* v_key_1851_; lean_object* v_value_1852_; lean_object* v_tail_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1865_; 
v_key_1851_ = lean_ctor_get(v_x_1850_, 0);
v_value_1852_ = lean_ctor_get(v_x_1850_, 1);
v_tail_1853_ = lean_ctor_get(v_x_1850_, 2);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_x_1850_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1855_ = v_x_1850_;
v_isShared_1856_ = v_isSharedCheck_1865_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_tail_1853_);
lean_inc(v_value_1852_);
lean_inc(v_key_1851_);
lean_dec(v_x_1850_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1865_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
uint8_t v___x_1857_; 
v___x_1857_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1851_, v_a_1848_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(v_a_1848_, v_b_1849_, v_tail_1853_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 2, v___x_1858_);
v___x_1860_ = v___x_1855_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_key_1851_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_value_1852_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
else
{
lean_object* v___x_1863_; 
lean_dec(v_value_1852_);
lean_dec(v_key_1851_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v_b_1849_);
lean_ctor_set(v___x_1855_, 0, v_a_1848_);
v___x_1863_ = v___x_1855_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1848_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_b_1849_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_tail_1853_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9___redArg(lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
return v_x_1866_;
}
else
{
lean_object* v_key_1868_; lean_object* v_value_1869_; lean_object* v_tail_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1893_; 
v_key_1868_ = lean_ctor_get(v_x_1867_, 0);
v_value_1869_ = lean_ctor_get(v_x_1867_, 1);
v_tail_1870_ = lean_ctor_get(v_x_1867_, 2);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_x_1867_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1872_ = v_x_1867_;
v_isShared_1873_ = v_isSharedCheck_1893_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_tail_1870_);
lean_inc(v_value_1869_);
lean_inc(v_key_1868_);
lean_dec(v_x_1867_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1893_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; uint64_t v___x_1875_; uint64_t v___x_1876_; uint64_t v___x_1877_; uint64_t v_fold_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; uint64_t v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; size_t v___x_1884_; size_t v___x_1885_; size_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1874_ = lean_array_get_size(v_x_1866_);
v___x_1875_ = l_Lean_Meta_DiscrTree_Key_hash(v_key_1868_);
v___x_1876_ = 32ULL;
v___x_1877_ = lean_uint64_shift_right(v___x_1875_, v___x_1876_);
v_fold_1878_ = lean_uint64_xor(v___x_1875_, v___x_1877_);
v___x_1879_ = 16ULL;
v___x_1880_ = lean_uint64_shift_right(v_fold_1878_, v___x_1879_);
v___x_1881_ = lean_uint64_xor(v_fold_1878_, v___x_1880_);
v___x_1882_ = lean_uint64_to_usize(v___x_1881_);
v___x_1883_ = lean_usize_of_nat(v___x_1874_);
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_sub(v___x_1883_, v___x_1884_);
v___x_1886_ = lean_usize_land(v___x_1882_, v___x_1885_);
v___x_1887_ = lean_array_uget_borrowed(v_x_1866_, v___x_1886_);
lean_inc(v___x_1887_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 2, v___x_1887_);
v___x_1889_ = v___x_1872_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_key_1868_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_value_1869_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_array_uset(v_x_1866_, v___x_1886_, v___x_1889_);
v_x_1866_ = v___x_1890_;
v_x_1867_ = v_tail_1870_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5___redArg(lean_object* v_i_1894_, lean_object* v_source_1895_, lean_object* v_target_1896_){
_start:
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = lean_array_get_size(v_source_1895_);
v___x_1898_ = lean_nat_dec_lt(v_i_1894_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_dec_ref(v_source_1895_);
lean_dec(v_i_1894_);
return v_target_1896_;
}
else
{
lean_object* v_es_1899_; lean_object* v___x_1900_; lean_object* v_source_1901_; lean_object* v_target_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_es_1899_ = lean_array_fget(v_source_1895_, v_i_1894_);
v___x_1900_ = lean_box(0);
v_source_1901_ = lean_array_fset(v_source_1895_, v_i_1894_, v___x_1900_);
v_target_1902_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9___redArg(v_target_1896_, v_es_1899_);
v___x_1903_ = lean_unsigned_to_nat(1u);
v___x_1904_ = lean_nat_add(v_i_1894_, v___x_1903_);
lean_dec(v_i_1894_);
v_i_1894_ = v___x_1904_;
v_source_1895_ = v_source_1901_;
v_target_1896_ = v_target_1902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4___redArg(lean_object* v_data_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_nbuckets_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1907_ = lean_array_get_size(v_data_1906_);
v___x_1908_ = lean_unsigned_to_nat(2u);
v_nbuckets_1909_ = lean_nat_mul(v___x_1907_, v___x_1908_);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_mk_array(v_nbuckets_1909_, v___x_1911_);
v___x_1913_ = lean_array_propagate_mark(v_data_1906_, v___x_1912_);
v___x_1914_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5___redArg(v___x_1910_, v_data_1906_, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(lean_object* v_a_1915_, lean_object* v_x_1916_){
_start:
{
if (lean_obj_tag(v_x_1916_) == 0)
{
uint8_t v___x_1917_; 
v___x_1917_ = 0;
return v___x_1917_;
}
else
{
lean_object* v_key_1918_; lean_object* v_tail_1919_; uint8_t v___x_1920_; 
v_key_1918_ = lean_ctor_get(v_x_1916_, 0);
v_tail_1919_ = lean_ctor_get(v_x_1916_, 2);
v___x_1920_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1918_, v_a_1915_);
if (v___x_1920_ == 0)
{
v_x_1916_ = v_tail_1919_;
goto _start;
}
else
{
return v___x_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg___boxed(lean_object* v_a_1922_, lean_object* v_x_1923_){
_start:
{
uint8_t v_res_1924_; lean_object* v_r_1925_; 
v_res_1924_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(v_a_1922_, v_x_1923_);
lean_dec(v_x_1923_);
lean_dec(v_a_1922_);
v_r_1925_ = lean_box(v_res_1924_);
return v_r_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2___redArg(lean_object* v_m_1926_, lean_object* v_a_1927_, lean_object* v_b_1928_){
_start:
{
lean_object* v_size_1929_; lean_object* v_buckets_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1973_; 
v_size_1929_ = lean_ctor_get(v_m_1926_, 0);
v_buckets_1930_ = lean_ctor_get(v_m_1926_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_m_1926_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1932_ = v_m_1926_;
v_isShared_1933_ = v_isSharedCheck_1973_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_buckets_1930_);
lean_inc(v_size_1929_);
lean_dec(v_m_1926_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1973_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; uint64_t v___x_1935_; uint64_t v___x_1936_; uint64_t v___x_1937_; uint64_t v_fold_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; size_t v___x_1942_; size_t v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; lean_object* v_bkt_1947_; uint8_t v___x_1948_; 
v___x_1934_ = lean_array_get_size(v_buckets_1930_);
v___x_1935_ = l_Lean_Meta_DiscrTree_Key_hash(v_a_1927_);
v___x_1936_ = 32ULL;
v___x_1937_ = lean_uint64_shift_right(v___x_1935_, v___x_1936_);
v_fold_1938_ = lean_uint64_xor(v___x_1935_, v___x_1937_);
v___x_1939_ = 16ULL;
v___x_1940_ = lean_uint64_shift_right(v_fold_1938_, v___x_1939_);
v___x_1941_ = lean_uint64_xor(v_fold_1938_, v___x_1940_);
v___x_1942_ = lean_uint64_to_usize(v___x_1941_);
v___x_1943_ = lean_usize_of_nat(v___x_1934_);
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_sub(v___x_1943_, v___x_1944_);
v___x_1946_ = lean_usize_land(v___x_1942_, v___x_1945_);
v_bkt_1947_ = lean_array_uget_borrowed(v_buckets_1930_, v___x_1946_);
v___x_1948_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(v_a_1927_, v_bkt_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v_size_x27_1950_; lean_object* v___x_1951_; lean_object* v_buckets_x27_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1949_ = lean_unsigned_to_nat(1u);
v_size_x27_1950_ = lean_nat_add(v_size_1929_, v___x_1949_);
lean_dec(v_size_1929_);
lean_inc(v_bkt_1947_);
v___x_1951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1951_, 0, v_a_1927_);
lean_ctor_set(v___x_1951_, 1, v_b_1928_);
lean_ctor_set(v___x_1951_, 2, v_bkt_1947_);
v_buckets_x27_1952_ = lean_array_uset(v_buckets_1930_, v___x_1946_, v___x_1951_);
v___x_1953_ = lean_unsigned_to_nat(4u);
v___x_1954_ = lean_nat_mul(v_size_x27_1950_, v___x_1953_);
v___x_1955_ = lean_unsigned_to_nat(3u);
v___x_1956_ = lean_nat_div(v___x_1954_, v___x_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_array_get_size(v_buckets_x27_1952_);
v___x_1958_ = lean_nat_dec_le(v___x_1956_, v___x_1957_);
lean_dec(v___x_1956_);
if (v___x_1958_ == 0)
{
lean_object* v_val_1959_; lean_object* v___x_1961_; 
v_val_1959_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4___redArg(v_buckets_x27_1952_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 1, v_val_1959_);
lean_ctor_set(v___x_1932_, 0, v_size_x27_1950_);
v___x_1961_ = v___x_1932_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_size_x27_1950_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_val_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
else
{
lean_object* v___x_1964_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 1, v_buckets_x27_1952_);
lean_ctor_set(v___x_1932_, 0, v_size_x27_1950_);
v___x_1964_ = v___x_1932_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_size_x27_1950_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_buckets_x27_1952_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v___x_1966_; lean_object* v_buckets_x27_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
lean_inc(v_bkt_1947_);
v___x_1966_ = lean_box(0);
v_buckets_x27_1967_ = lean_array_uset(v_buckets_1930_, v___x_1946_, v___x_1966_);
v___x_1968_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(v_a_1927_, v_b_1928_, v_bkt_1947_);
v___x_1969_ = lean_array_uset(v_buckets_x27_1967_, v___x_1946_, v___x_1968_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 1, v___x_1969_);
v___x_1971_ = v___x_1932_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_size_1929_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(lean_object* v_a_1974_, lean_object* v_x_1975_){
_start:
{
if (lean_obj_tag(v_x_1975_) == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_box(0);
return v___x_1976_;
}
else
{
lean_object* v_key_1977_; lean_object* v_value_1978_; lean_object* v_tail_1979_; uint8_t v___x_1980_; 
v_key_1977_ = lean_ctor_get(v_x_1975_, 0);
v_value_1978_ = lean_ctor_get(v_x_1975_, 1);
v_tail_1979_ = lean_ctor_get(v_x_1975_, 2);
v___x_1980_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1977_, v_a_1974_);
if (v___x_1980_ == 0)
{
v_x_1975_ = v_tail_1979_;
goto _start;
}
else
{
lean_object* v___x_1982_; 
lean_inc(v_value_1978_);
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_value_1978_);
return v___x_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg___boxed(lean_object* v_a_1983_, lean_object* v_x_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(v_a_1983_, v_x_1984_);
lean_dec(v_x_1984_);
lean_dec(v_a_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(lean_object* v_m_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v_buckets_1988_; lean_object* v___x_1989_; uint64_t v___x_1990_; uint64_t v___x_1991_; uint64_t v___x_1992_; uint64_t v_fold_1993_; uint64_t v___x_1994_; uint64_t v___x_1995_; uint64_t v___x_1996_; size_t v___x_1997_; size_t v___x_1998_; size_t v___x_1999_; size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v_buckets_1988_ = lean_ctor_get(v_m_1986_, 1);
v___x_1989_ = lean_array_get_size(v_buckets_1988_);
v___x_1990_ = l_Lean_Meta_DiscrTree_Key_hash(v_a_1987_);
v___x_1991_ = 32ULL;
v___x_1992_ = lean_uint64_shift_right(v___x_1990_, v___x_1991_);
v_fold_1993_ = lean_uint64_xor(v___x_1990_, v___x_1992_);
v___x_1994_ = 16ULL;
v___x_1995_ = lean_uint64_shift_right(v_fold_1993_, v___x_1994_);
v___x_1996_ = lean_uint64_xor(v_fold_1993_, v___x_1995_);
v___x_1997_ = lean_uint64_to_usize(v___x_1996_);
v___x_1998_ = lean_usize_of_nat(v___x_1989_);
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_sub(v___x_1998_, v___x_1999_);
v___x_2001_ = lean_usize_land(v___x_1997_, v___x_2000_);
v___x_2002_ = lean_array_uget_borrowed(v_buckets_1988_, v___x_2001_);
v___x_2003_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(v_a_1987_, v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg___boxed(lean_object* v_m_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(v_m_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_m_2004_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2011_ == 0)
{
return v_b_2010_;
}
else
{
lean_object* v_snd_2012_; lean_object* v_fst_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2081_; 
v_snd_2012_ = lean_ctor_get(v_b_2010_, 1);
v_fst_2013_ = lean_ctor_get(v_b_2010_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_b_2010_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2015_ = v_b_2010_;
v_isShared_2016_ = v_isSharedCheck_2081_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_snd_2012_);
lean_inc(v_fst_2013_);
lean_dec(v_b_2010_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2081_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_fst_2017_; lean_object* v_snd_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2080_; 
v_fst_2017_ = lean_ctor_get(v_snd_2012_, 0);
v_snd_2018_ = lean_ctor_get(v_snd_2012_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_snd_2012_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2020_ = v_snd_2012_;
v_isShared_2021_ = v_isSharedCheck_2080_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_snd_2018_);
lean_inc(v_fst_2017_);
lean_dec(v_snd_2012_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2080_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_idx_2023_; lean_object* v_groups_2024_; lean_object* v_a_2036_; lean_object* v_fst_2037_; lean_object* v_snd_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2079_; 
v_a_2036_ = lean_array_uget(v_as_2007_, v_i_2009_);
v_fst_2037_ = lean_ctor_get(v_a_2036_, 0);
v_snd_2038_ = lean_ctor_get(v_a_2036_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_a_2036_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2040_ = v_a_2036_;
v_isShared_2041_ = v_isSharedCheck_2079_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_snd_2038_);
lean_inc(v_fst_2037_);
lean_dec(v_a_2036_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2079_;
goto v_resetjp_2039_;
}
v___jp_2022_:
{
lean_object* v___x_2025_; lean_object* v_pos_2026_; lean_object* v___x_2028_; 
v___x_2025_ = lean_unsigned_to_nat(1u);
v_pos_2026_ = lean_nat_add(v_snd_2018_, v___x_2025_);
lean_dec(v_snd_2018_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v_pos_2026_);
lean_ctor_set(v___x_2020_, 0, v_groups_2024_);
v___x_2028_ = v___x_2020_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_groups_2024_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_pos_2026_);
v___x_2028_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v___x_2028_);
lean_ctor_set(v___x_2015_, 0, v_idx_2023_);
v___x_2030_ = v___x_2015_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_idx_2023_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
size_t v___x_2031_; size_t v___x_2032_; 
v___x_2031_ = ((size_t)1ULL);
v___x_2032_ = lean_usize_add(v_i_2009_, v___x_2031_);
v_i_2009_ = v___x_2032_;
v_b_2010_ = v___x_2030_;
goto _start;
}
}
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(v_fst_2013_, v_fst_2037_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2043_; lean_object* v_idx_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2043_ = lean_array_get_size(v_fst_2017_);
lean_inc(v_fst_2037_);
v_idx_2044_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2___redArg(v_fst_2013_, v_fst_2037_, v___x_2043_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_mk_empty_array_with_capacity(v___x_2045_);
v___x_2047_ = lean_array_push(v___x_2046_, v_snd_2038_);
lean_inc(v_snd_2018_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 1, v_snd_2018_);
lean_ctor_set(v___x_2040_, 0, v___x_2047_);
v___x_2049_ = v___x_2040_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_snd_2018_);
v___x_2049_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v_groups_2051_; 
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_fst_2037_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v_groups_2051_ = lean_array_push(v_fst_2017_, v___x_2050_);
v_idx_2023_ = v_idx_2044_;
v_groups_2024_ = v_groups_2051_;
goto v___jp_2022_;
}
}
else
{
lean_object* v_val_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
lean_del_object(v___x_2040_);
lean_dec(v_fst_2037_);
v_val_2053_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_val_2053_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2054_ = lean_array_get_size(v_fst_2017_);
v___x_2055_ = lean_nat_dec_lt(v_val_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_dec(v_val_2053_);
lean_dec(v_snd_2038_);
v_idx_2023_ = v_fst_2013_;
v_groups_2024_ = v_fst_2017_;
goto v___jp_2022_;
}
else
{
lean_object* v_v_2056_; lean_object* v_snd_2057_; lean_object* v_fst_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2078_; 
v_v_2056_ = lean_array_fget(v_fst_2017_, v_val_2053_);
v_snd_2057_ = lean_ctor_get(v_v_2056_, 1);
v_fst_2058_ = lean_ctor_get(v_v_2056_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_v_2056_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2060_ = v_v_2056_;
v_isShared_2061_ = v_isSharedCheck_2078_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_snd_2057_);
lean_inc(v_fst_2058_);
lean_dec(v_v_2056_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2078_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_fst_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2076_; 
v_fst_2062_ = lean_ctor_get(v_snd_2057_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_snd_2057_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_snd_2057_, 1);
lean_dec(v_unused_2077_);
v___x_2064_ = v_snd_2057_;
v_isShared_2065_ = v_isSharedCheck_2076_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_fst_2062_);
lean_dec(v_snd_2057_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2076_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v_xs_x27_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2066_ = lean_box(0);
v_xs_x27_2067_ = lean_array_fset(v_fst_2017_, v_val_2053_, v___x_2066_);
v___x_2068_ = lean_array_push(v_fst_2062_, v_snd_2038_);
lean_inc(v_snd_2018_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v_snd_2018_);
lean_ctor_set(v___x_2064_, 0, v___x_2068_);
v___x_2070_ = v___x_2064_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_snd_2018_);
v___x_2070_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___x_2070_);
v___x_2072_ = v___x_2060_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_fst_2058_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_array_fset(v_xs_x27_2067_, v_val_2053_, v___x_2072_);
lean_dec(v_val_2053_);
v_idx_2023_ = v_fst_2013_;
v_groups_2024_ = v___x_2073_;
goto v___jp_2022_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg___boxed(lean_object* v_as_2082_, lean_object* v_sz_2083_, lean_object* v_i_2084_, lean_object* v_b_2085_){
_start:
{
size_t v_sz_boxed_2086_; size_t v_i_boxed_2087_; lean_object* v_res_2088_; 
v_sz_boxed_2086_ = lean_unbox_usize(v_sz_2083_);
lean_dec(v_sz_2083_);
v_i_boxed_2087_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_res_2088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(v_as_2082_, v_sz_boxed_2086_, v_i_boxed_2087_, v_b_2085_);
lean_dec_ref(v_as_2082_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(lean_object* v_as_2089_, size_t v_sz_2090_, size_t v_i_2091_, lean_object* v_b_2092_){
_start:
{
uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_lt(v_i_2091_, v_sz_2090_);
if (v___x_2093_ == 0)
{
return v_b_2092_;
}
else
{
lean_object* v_snd_2094_; lean_object* v_fst_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2136_; 
v_snd_2094_ = lean_ctor_get(v_b_2092_, 1);
v_fst_2095_ = lean_ctor_get(v_b_2092_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_b_2092_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2097_ = v_b_2092_;
v_isShared_2098_ = v_isSharedCheck_2136_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_snd_2094_);
lean_inc(v_fst_2095_);
lean_dec(v_b_2092_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2136_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_fst_2099_; lean_object* v_snd_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2135_; 
v_fst_2099_ = lean_ctor_get(v_snd_2094_, 0);
v_snd_2100_ = lean_ctor_get(v_snd_2094_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_snd_2094_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2102_ = v_snd_2094_;
v_isShared_2103_ = v_isSharedCheck_2135_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_snd_2100_);
lean_inc(v_fst_2099_);
lean_dec(v_snd_2094_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2135_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_a_2104_; lean_object* v___x_2106_; 
v_a_2104_ = lean_array_uget_borrowed(v_as_2089_, v_i_2091_);
if (v_isShared_2103_ == 0)
{
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_fst_2099_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_snd_2100_);
v___x_2106_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2106_);
v___x_2108_ = v___x_2097_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_fst_2095_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
size_t v_sz_2109_; size_t v___x_2110_; lean_object* v___x_2111_; lean_object* v_snd_2112_; lean_object* v_fst_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2132_; 
v_sz_2109_ = lean_array_size(v_a_2104_);
v___x_2110_ = ((size_t)0ULL);
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(v_a_2104_, v_sz_2109_, v___x_2110_, v___x_2108_);
v_snd_2112_ = lean_ctor_get(v___x_2111_, 1);
v_fst_2113_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2115_ = v___x_2111_;
v_isShared_2116_ = v_isSharedCheck_2132_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_snd_2112_);
lean_inc(v_fst_2113_);
lean_dec(v___x_2111_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2132_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_fst_2117_; lean_object* v_snd_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2131_; 
v_fst_2117_ = lean_ctor_get(v_snd_2112_, 0);
v_snd_2118_ = lean_ctor_get(v_snd_2112_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_snd_2112_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2120_ = v_snd_2112_;
v_isShared_2121_ = v_isSharedCheck_2131_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snd_2118_);
lean_inc(v_fst_2117_);
lean_dec(v_snd_2112_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2131_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_fst_2117_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_snd_2118_);
v___x_2123_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v___x_2123_);
v___x_2125_ = v___x_2115_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_fst_2113_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
size_t v___x_2126_; size_t v___x_2127_; 
v___x_2126_ = ((size_t)1ULL);
v___x_2127_ = lean_usize_add(v_i_2091_, v___x_2126_);
v_i_2091_ = v___x_2127_;
v_b_2092_ = v___x_2125_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg___boxed(lean_object* v_as_2137_, lean_object* v_sz_2138_, lean_object* v_i_2139_, lean_object* v_b_2140_){
_start:
{
size_t v_sz_boxed_2141_; size_t v_i_boxed_2142_; lean_object* v_res_2143_; 
v_sz_boxed_2141_ = lean_unbox_usize(v_sz_2138_);
lean_dec(v_sz_2138_);
v_i_boxed_2142_ = lean_unbox_usize(v_i_2139_);
lean_dec(v_i_2139_);
v_res_2143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(v_as_2137_, v_sz_boxed_2141_, v_i_boxed_2142_, v_b_2140_);
lean_dec_ref(v_as_2137_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(size_t v_sz_2144_, size_t v_i_2145_, lean_object* v_bs_2146_){
_start:
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_usize_dec_lt(v_i_2145_, v_sz_2144_);
if (v___x_2147_ == 0)
{
return v_bs_2146_;
}
else
{
lean_object* v_v_2148_; lean_object* v_snd_2149_; lean_object* v_fst_2150_; lean_object* v_fst_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2164_; 
v_v_2148_ = lean_array_uget_borrowed(v_bs_2146_, v_i_2145_);
v_snd_2149_ = lean_ctor_get(v_v_2148_, 1);
lean_inc(v_snd_2149_);
v_fst_2150_ = lean_ctor_get(v_v_2148_, 0);
lean_inc(v_fst_2150_);
v_fst_2151_ = lean_ctor_get(v_snd_2149_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_snd_2149_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v_snd_2149_, 1);
lean_dec(v_unused_2165_);
v___x_2153_ = v_snd_2149_;
v_isShared_2154_ = v_isSharedCheck_2164_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_fst_2151_);
lean_dec(v_snd_2149_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2164_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v_bs_x27_2156_; lean_object* v___x_2158_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v_bs_x27_2156_ = lean_array_uset(v_bs_2146_, v_i_2145_, v___x_2155_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v_fst_2151_);
lean_ctor_set(v___x_2153_, 0, v_fst_2150_);
v___x_2158_ = v___x_2153_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_fst_2150_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_fst_2151_);
v___x_2158_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
size_t v___x_2159_; size_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2145_, v___x_2159_);
v___x_2161_ = lean_array_uset(v_bs_x27_2156_, v_i_2145_, v___x_2158_);
v_i_2145_ = v___x_2160_;
v_bs_2146_ = v___x_2161_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg___boxed(lean_object* v_sz_2166_, lean_object* v_i_2167_, lean_object* v_bs_2168_){
_start:
{
size_t v_sz_boxed_2169_; size_t v_i_boxed_2170_; lean_object* v_res_2171_; 
v_sz_boxed_2169_ = lean_unbox_usize(v_sz_2166_);
lean_dec(v_sz_2166_);
v_i_boxed_2170_ = lean_unbox_usize(v_i_2167_);
lean_dec(v_i_2167_);
v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(v_sz_boxed_2169_, v_i_boxed_2170_, v_bs_2168_);
return v_res_2171_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_box(0);
v___x_2173_ = lean_unsigned_to_nat(16u);
v___x_2174_ = lean_mk_array(v___x_2173_, v___x_2172_);
return v___x_2174_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v_idx_2177_; 
v___x_2175_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__0);
v___x_2176_ = lean_unsigned_to_nat(0u);
v_idx_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_idx_2177_, 0, v___x_2176_);
lean_ctor_set(v_idx_2177_, 1, v___x_2175_);
return v_idx_2177_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4(void){
_start:
{
lean_object* v___x_2183_; lean_object* v_idx_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__3));
v_idx_2184_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1);
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_idx_2184_);
lean_ctor_set(v___x_2185_, 1, v___x_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(lean_object* v_ts_2186_){
_start:
{
lean_object* v___y_2188_; lean_object* v___x_2192_; lean_object* v___x_2193_; size_t v_sz_2194_; size_t v___x_2195_; lean_object* v___x_2196_; lean_object* v_snd_2197_; lean_object* v_fst_2198_; lean_object* v___x_2199_; lean_object* v___y_2201_; lean_object* v___y_2202_; uint8_t v___x_2204_; 
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__4);
v_sz_2194_ = lean_array_size(v_ts_2186_);
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(v_ts_2186_, v_sz_2194_, v___x_2195_, v___x_2193_);
v_snd_2197_ = lean_ctor_get(v___x_2196_, 1);
lean_inc(v_snd_2197_);
lean_dec_ref(v___x_2196_);
v_fst_2198_ = lean_ctor_get(v_snd_2197_, 0);
lean_inc(v_fst_2198_);
lean_dec(v_snd_2197_);
v___x_2199_ = lean_array_get_size(v_fst_2198_);
v___x_2204_ = lean_nat_dec_eq(v___x_2199_, v___x_2192_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___y_2208_; uint8_t v___x_2210_; 
v___x_2205_ = lean_unsigned_to_nat(1u);
v___x_2206_ = lean_nat_sub(v___x_2199_, v___x_2205_);
v___x_2210_ = lean_nat_dec_le(v___x_2192_, v___x_2206_);
if (v___x_2210_ == 0)
{
lean_inc(v___x_2206_);
v___y_2208_ = v___x_2206_;
goto v___jp_2207_;
}
else
{
v___y_2208_ = v___x_2192_;
goto v___jp_2207_;
}
v___jp_2207_:
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_nat_dec_le(v___y_2208_, v___x_2206_);
if (v___x_2209_ == 0)
{
lean_dec(v___x_2206_);
lean_inc(v___y_2208_);
v___y_2201_ = v___y_2208_;
v___y_2202_ = v___y_2208_;
goto v___jp_2200_;
}
else
{
v___y_2201_ = v___y_2208_;
v___y_2202_ = v___x_2206_;
goto v___jp_2200_;
}
}
}
else
{
v___y_2188_ = v_fst_2198_;
goto v___jp_2187_;
}
v___jp_2187_:
{
size_t v_sz_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v_sz_2189_ = lean_array_size(v___y_2188_);
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(v_sz_2189_, v___x_2190_, v___y_2188_);
return v___x_2191_;
}
v___jp_2200_:
{
lean_object* v___x_2203_; 
v___x_2203_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(v___x_2199_, v_fst_2198_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
v___y_2188_ = v___x_2203_;
goto v___jp_2187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___boxed(lean_object* v_ts_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(v_ts_2211_);
lean_dec_ref(v_ts_2211_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey(lean_object* v_00_u03b1_2213_, lean_object* v_ts_2214_, lean_object* v_P_2215_, lean_object* v_hP_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(v_ts_2214_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_ts_2219_, lean_object* v_P_2220_, lean_object* v_hP_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey(v_00_u03b1_2218_, v_ts_2219_, v_P_2220_, v_hP_2221_);
lean_dec_ref(v_ts_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0(lean_object* v_00_u03b1_2223_, size_t v_sz_2224_, size_t v_i_2225_, lean_object* v_bs_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___redArg(v_sz_2224_, v_i_2225_, v_bs_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0___boxed(lean_object* v_00_u03b1_2228_, lean_object* v_sz_2229_, lean_object* v_i_2230_, lean_object* v_bs_2231_){
_start:
{
size_t v_sz_boxed_2232_; size_t v_i_boxed_2233_; lean_object* v_res_2234_; 
v_sz_boxed_2232_ = lean_unbox_usize(v_sz_2229_);
lean_dec(v_sz_2229_);
v_i_boxed_2233_ = lean_unbox_usize(v_i_2230_);
lean_dec(v_i_2230_);
v_res_2234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__0(v_00_u03b1_2228_, v_sz_boxed_2232_, v_i_boxed_2233_, v_bs_2231_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1(lean_object* v_00_u03b2_2235_, lean_object* v_m_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___redArg(v_m_2236_, v_a_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1___boxed(lean_object* v_00_u03b2_2239_, lean_object* v_m_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1(v_00_u03b2_2239_, v_m_2240_, v_a_2241_);
lean_dec(v_a_2241_);
lean_dec_ref(v_m_2240_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2(lean_object* v_00_u03b2_2243_, lean_object* v_m_2244_, lean_object* v_a_2245_, lean_object* v_b_2246_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2___redArg(v_m_2244_, v_a_2245_, v_b_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3(lean_object* v_00_u03b1_2248_, lean_object* v_as_2249_, size_t v_sz_2250_, size_t v_i_2251_, lean_object* v_b_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___redArg(v_as_2249_, v_sz_2250_, v_i_2251_, v_b_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_as_2255_, lean_object* v_sz_2256_, lean_object* v_i_2257_, lean_object* v_b_2258_){
_start:
{
size_t v_sz_boxed_2259_; size_t v_i_boxed_2260_; lean_object* v_res_2261_; 
v_sz_boxed_2259_ = lean_unbox_usize(v_sz_2256_);
lean_dec(v_sz_2256_);
v_i_boxed_2260_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__3(v_00_u03b1_2254_, v_as_2255_, v_sz_boxed_2259_, v_i_boxed_2260_, v_b_2258_);
lean_dec_ref(v_as_2255_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4(lean_object* v_00_u03b1_2262_, lean_object* v_as_2263_, size_t v_sz_2264_, size_t v_i_2265_, lean_object* v_b_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___redArg(v_as_2263_, v_sz_2264_, v_i_2265_, v_b_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_as_2269_, lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_b_2272_){
_start:
{
size_t v_sz_boxed_2273_; size_t v_i_boxed_2274_; lean_object* v_res_2275_; 
v_sz_boxed_2273_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2274_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__4(v_00_u03b1_2268_, v_as_2269_, v_sz_boxed_2273_, v_i_boxed_2274_, v_b_2272_);
lean_dec_ref(v_as_2269_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5(lean_object* v_00_u03b1_2276_, lean_object* v_n_2277_, lean_object* v_as_2278_, lean_object* v_lo_2279_, lean_object* v_hi_2280_, lean_object* v_w_2281_, lean_object* v_hlo_2282_, lean_object* v_hhi_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___redArg(v_n_2277_, v_as_2278_, v_lo_2279_, v_hi_2280_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_n_2286_, lean_object* v_as_2287_, lean_object* v_lo_2288_, lean_object* v_hi_2289_, lean_object* v_w_2290_, lean_object* v_hlo_2291_, lean_object* v_hhi_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5(v_00_u03b1_2285_, v_n_2286_, v_as_2287_, v_lo_2288_, v_hi_2289_, v_w_2290_, v_hlo_2291_, v_hhi_2292_);
lean_dec(v_hi_2289_);
lean_dec(v_n_2286_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1(lean_object* v_00_u03b2_2294_, lean_object* v_a_2295_, lean_object* v_x_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___redArg(v_a_2295_, v_x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2298_, lean_object* v_a_2299_, lean_object* v_x_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__1_spec__1(v_00_u03b2_2298_, v_a_2299_, v_x_2300_);
lean_dec(v_x_2300_);
lean_dec(v_a_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3(lean_object* v_00_u03b2_2302_, lean_object* v_a_2303_, lean_object* v_x_2304_){
_start:
{
uint8_t v___x_2305_; 
v___x_2305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___redArg(v_a_2303_, v_x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2306_, lean_object* v_a_2307_, lean_object* v_x_2308_){
_start:
{
uint8_t v_res_2309_; lean_object* v_r_2310_; 
v_res_2309_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__3(v_00_u03b2_2306_, v_a_2307_, v_x_2308_);
lean_dec(v_x_2308_);
lean_dec(v_a_2307_);
v_r_2310_ = lean_box(v_res_2309_);
return v_r_2310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4(lean_object* v_00_u03b2_2311_, lean_object* v_data_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4___redArg(v_data_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5(lean_object* v_00_u03b2_2314_, lean_object* v_a_2315_, lean_object* v_b_2316_, lean_object* v_x_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__5___redArg(v_a_2315_, v_b_2316_, v_x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9(lean_object* v_00_u03b1_2319_, lean_object* v_n_2320_, lean_object* v_lo_2321_, lean_object* v_hi_2322_, lean_object* v_hhi_2323_, lean_object* v_pivot_2324_, lean_object* v_as_2325_, lean_object* v_i_2326_, lean_object* v_k_2327_, lean_object* v_ilo_2328_, lean_object* v_ik_2329_, lean_object* v_w_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___redArg(v_hi_2322_, v_pivot_2324_, v_as_2325_, v_i_2326_, v_k_2327_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9___boxed(lean_object* v_00_u03b1_2332_, lean_object* v_n_2333_, lean_object* v_lo_2334_, lean_object* v_hi_2335_, lean_object* v_hhi_2336_, lean_object* v_pivot_2337_, lean_object* v_as_2338_, lean_object* v_i_2339_, lean_object* v_k_2340_, lean_object* v_ilo_2341_, lean_object* v_ik_2342_, lean_object* v_w_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__5_spec__9(v_00_u03b1_2332_, v_n_2333_, v_lo_2334_, v_hi_2335_, v_hhi_2336_, v_pivot_2337_, v_as_2338_, v_i_2339_, v_k_2340_, v_ilo_2341_, v_ik_2342_, v_w_2343_);
lean_dec_ref(v_pivot_2337_);
lean_dec(v_hi_2335_);
lean_dec(v_lo_2334_);
lean_dec(v_n_2333_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2345_, lean_object* v_i_2346_, lean_object* v_source_2347_, lean_object* v_target_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5___redArg(v_i_2346_, v_source_2347_, v_target_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey_spec__2_spec__4_spec__5_spec__9___redArg(v_x_2351_, v_x_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0(lean_object* v_x_2354_){
_start:
{
lean_object* v_snd_2355_; 
v_snd_2355_ = lean_ctor_get(v_x_2354_, 1);
lean_inc(v_snd_2355_);
return v_snd_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0___boxed(lean_object* v_x_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__0(v_x_2356_);
lean_dec_ref(v_x_2356_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__4(lean_object* v___f_2358_, lean_object* v_x1_2359_, lean_object* v_x2_2360_){
_start:
{
lean_object* v_fst_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_fst_2361_ = lean_ctor_get(v_x2_2360_, 0);
lean_inc(v_fst_2361_);
lean_dec_ref(v_x2_2360_);
v___x_2362_ = lean_array_get_size(v_x1_2359_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = lean_nat_dec_eq(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2365_ = lean_array_get_size(v_fst_2361_);
v___x_2366_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v___x_2367_ = lean_nat_dec_lt(v___x_2363_, v___x_2365_);
if (v___x_2367_ == 0)
{
lean_dec(v_fst_2361_);
lean_dec_ref(v___f_2358_);
return v_x1_2359_;
}
else
{
size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
v___x_2368_ = ((size_t)0ULL);
v___x_2369_ = lean_usize_of_nat(v___x_2365_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2366_, v___f_2358_, v_fst_2361_, v___x_2368_, v___x_2369_, v_x1_2359_);
return v___x_2370_;
}
}
else
{
lean_dec_ref(v_x1_2359_);
lean_dec_ref(v___f_2358_);
return v_fst_2361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__3(lean_object* v_inst_2371_, lean_object* v_x1_2372_, lean_object* v_x2_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_2371_, v_x1_2372_, v_x2_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2(lean_object* v_x1_2375_, lean_object* v_x2_2376_){
_start:
{
lean_object* v_fst_2377_; lean_object* v_fst_2378_; uint8_t v___x_2379_; 
v_fst_2377_ = lean_ctor_get(v_x1_2375_, 0);
v_fst_2378_ = lean_ctor_get(v_x2_2376_, 0);
v___x_2379_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_2377_, v_fst_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2___boxed(lean_object* v_x1_2380_, lean_object* v_x2_2381_){
_start:
{
uint8_t v_res_2382_; lean_object* v_r_2383_; 
v_res_2382_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__2(v_x1_2380_, v_x2_2381_);
lean_dec_ref(v_x2_2381_);
lean_dec_ref(v_x1_2380_);
v_r_2383_ = lean_box(v_res_2382_);
return v_r_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(lean_object* v_inst_2386_, lean_object* v_g_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2388_ = lean_array_get_size(v_g_2387_);
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = lean_nat_dec_eq(v___x_2388_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___f_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___f_2391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2391_, 0, v_inst_2386_);
lean_closure_set(v___f_2391_, 1, v_g_2387_);
v___x_2392_ = lean_mk_thunk(v___f_2391_);
v___x_2393_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
return v___x_2393_;
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec_ref(v_inst_2386_);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_array_fget(v_g_2387_, v___x_2394_);
lean_dec_ref(v_g_2387_);
return v___x_2395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__1(lean_object* v_inst_2396_, lean_object* v_x_2397_){
_start:
{
lean_object* v_fst_2398_; lean_object* v_snd_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2407_; 
v_fst_2398_ = lean_ctor_get(v_x_2397_, 0);
v_snd_2399_ = lean_ctor_get(v_x_2397_, 1);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_x_2397_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2401_ = v_x_2397_;
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_snd_2399_);
lean_inc(v_fst_2398_);
lean_dec(v_x_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(v_inst_2396_, v_snd_2399_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 1, v___x_2403_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_fst_2398_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg(lean_object* v_inst_2409_, lean_object* v_ts_2410_){
_start:
{
lean_object* v___f_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___f_2414_; lean_object* v___x_2415_; size_t v_sz_2416_; size_t v___x_2417_; lean_object* v_nodes_2418_; lean_object* v___x_2419_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2459_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___f_2411_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__0));
v___f_2412_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__1));
lean_inc_ref(v_inst_2409_);
v___f_2413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2413_, 0, v_inst_2409_);
v___f_2414_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___closed__2));
v___x_2415_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v_sz_2416_ = lean_array_size(v_ts_2410_);
v___x_2417_ = ((size_t)0ULL);
v_nodes_2418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2415_, v___f_2411_, v_sz_2416_, v___x_2417_, v_ts_2410_);
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2468_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
v___x_2469_ = lean_array_get_size(v_nodes_2418_);
v___x_2470_ = lean_nat_dec_lt(v___x_2419_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec_ref(v_inst_2409_);
v___y_2459_ = v___x_2468_;
goto v___jp_2458_;
}
else
{
lean_object* v___f_2471_; lean_object* v___f_2472_; size_t v___x_2473_; lean_object* v___x_2474_; 
v___f_2471_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__3), 3, 1);
lean_closure_set(v___f_2471_, 0, v_inst_2409_);
v___f_2472_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg___lam__4), 3, 1);
lean_closure_set(v___f_2472_, 0, v___f_2471_);
v___x_2473_ = lean_usize_of_nat(v___x_2469_);
lean_inc(v_nodes_2418_);
v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2415_, v___f_2472_, v_nodes_2418_, v___x_2417_, v___x_2473_, v___x_2468_);
v___y_2459_ = v___x_2474_;
goto v___jp_2458_;
}
v___jp_2420_:
{
size_t v_sz_2424_; lean_object* v_cs_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v_sz_2424_ = lean_array_size(v___y_2423_);
v_cs_2425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2415_, v___f_2413_, v_sz_2424_, v___x_2417_, v___y_2423_);
v___x_2426_ = lean_array_get_size(v___y_2422_);
v___x_2427_ = lean_nat_dec_eq(v___x_2426_, v___x_2419_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___y_2422_);
lean_ctor_set(v___x_2428_, 1, v_cs_2425_);
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = lean_array_get_size(v_cs_2425_);
v___x_2430_ = lean_nat_dec_eq(v___x_2429_, v___y_2421_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___y_2422_);
lean_ctor_set(v___x_2431_, 1, v_cs_2425_);
return v___x_2431_;
}
else
{
lean_object* v___x_2432_; lean_object* v_fst_2433_; lean_object* v_snd_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v___y_2422_);
v___x_2432_ = lean_array_fget(v_cs_2425_, v___x_2419_);
lean_dec(v_cs_2425_);
v_fst_2433_ = lean_ctor_get(v___x_2432_, 0);
v_snd_2434_ = lean_ctor_get(v___x_2432_, 1);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2432_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_snd_2434_);
lean_inc(v_fst_2433_);
lean_dec(v___x_2432_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_fst_2433_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_snd_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
v___jp_2442_:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2414_, v___y_2447_, v___y_2445_, v___y_2446_, v___y_2448_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2448_);
lean_dec(v___y_2447_);
v___y_2421_ = v___y_2444_;
v___y_2422_ = v___y_2443_;
v___y_2423_ = v___x_2449_;
goto v___jp_2420_;
}
v___jp_2450_:
{
uint8_t v___x_2457_; 
v___x_2457_ = lean_nat_dec_le(v___y_2456_, v___y_2454_);
if (v___x_2457_ == 0)
{
lean_dec(v___y_2454_);
lean_inc(v___y_2456_);
v___y_2443_ = v___y_2453_;
v___y_2444_ = v___y_2452_;
v___y_2445_ = v___y_2451_;
v___y_2446_ = v___y_2456_;
v___y_2447_ = v___y_2455_;
v___y_2448_ = v___y_2456_;
goto v___jp_2442_;
}
else
{
v___y_2443_ = v___y_2453_;
v___y_2444_ = v___y_2452_;
v___y_2445_ = v___y_2451_;
v___y_2446_ = v___y_2456_;
v___y_2447_ = v___y_2455_;
v___y_2448_ = v___y_2454_;
goto v___jp_2442_;
}
}
v___jp_2458_:
{
size_t v_sz_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v_sz_2460_ = lean_array_size(v_nodes_2418_);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2415_, v___f_2412_, v_sz_2460_, v___x_2417_, v_nodes_2418_);
v___x_2462_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(v___x_2461_);
lean_dec(v___x_2461_);
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_array_get_size(v___x_2462_);
v___x_2465_ = lean_nat_dec_eq(v___x_2464_, v___x_2419_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_nat_sub(v___x_2464_, v___x_2463_);
v___x_2467_ = lean_nat_dec_le(v___x_2419_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_inc(v___x_2466_);
v___y_2451_ = v___x_2462_;
v___y_2452_ = v___x_2463_;
v___y_2453_ = v___y_2459_;
v___y_2454_ = v___x_2466_;
v___y_2455_ = v___x_2464_;
v___y_2456_ = v___x_2466_;
goto v___jp_2450_;
}
else
{
v___y_2451_ = v___x_2462_;
v___y_2452_ = v___x_2463_;
v___y_2453_ = v___y_2459_;
v___y_2454_ = v___x_2466_;
v___y_2455_ = v___x_2464_;
v___y_2456_ = v___x_2419_;
goto v___jp_2450_;
}
}
else
{
v___y_2421_ = v___x_2463_;
v___y_2422_ = v___y_2459_;
v___y_2423_ = v___x_2462_;
goto v___jp_2420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg___lam__0(lean_object* v_inst_2475_, lean_object* v_g_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg(v_inst_2475_, v_g_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries(lean_object* v_00_u03b1_2479_, lean_object* v_inst_2480_, lean_object* v_ts_2481_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries___redArg(v_inst_2480_, v_ts_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup(lean_object* v_00_u03b1_2483_, lean_object* v_inst_2484_, lean_object* v_g_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(v_inst_2484_, v_g_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries_match__1_splitter___redArg(lean_object* v_x_2487_, lean_object* v_h__1_2488_){
_start:
{
lean_object* v_fst_2489_; lean_object* v_snd_2490_; lean_object* v___x_2491_; 
v_fst_2489_ = lean_ctor_get(v_x_2487_, 0);
lean_inc(v_fst_2489_);
v_snd_2490_ = lean_ctor_get(v_x_2487_, 1);
lean_inc(v_snd_2490_);
lean_dec_ref(v_x_2487_);
v___x_2491_ = lean_apply_2(v_h__1_2488_, v_fst_2489_, v_snd_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeTries_match__1_splitter(lean_object* v_00_u03b1_2492_, lean_object* v_motive_2493_, lean_object* v_x_2494_, lean_object* v_h__1_2495_){
_start:
{
lean_object* v_fst_2496_; lean_object* v_snd_2497_; lean_object* v___x_2498_; 
v_fst_2496_ = lean_ctor_get(v_x_2494_, 0);
lean_inc(v_fst_2496_);
v_snd_2497_ = lean_ctor_get(v_x_2494_, 1);
lean_inc(v_snd_2497_);
lean_dec_ref(v_x_2494_);
v___x_2498_ = lean_apply_2(v_h__1_2495_, v_fst_2496_, v_snd_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0(lean_object* v_inst_2499_, lean_object* v___x_2500_, lean_object* v___x_2501_, lean_object* v___x_2502_, lean_object* v_a_2503_, lean_object* v_x_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_snd_2506_; lean_object* v_fst_2507_; lean_object* v_snd_2508_; lean_object* v_fst_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2535_; 
v_snd_2506_ = lean_ctor_get(v___y_2505_, 1);
lean_inc(v_snd_2506_);
v_fst_2507_ = lean_ctor_get(v_a_2503_, 0);
lean_inc(v_fst_2507_);
v_snd_2508_ = lean_ctor_get(v_a_2503_, 1);
lean_inc(v_snd_2508_);
lean_dec_ref(v_a_2503_);
v_fst_2509_ = lean_ctor_get(v___y_2505_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___y_2505_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v___y_2505_, 1);
lean_dec(v_unused_2536_);
v___x_2511_ = v___y_2505_;
v_isShared_2512_ = v_isSharedCheck_2535_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_fst_2509_);
lean_dec(v___y_2505_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2535_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2534_; 
v_fst_2513_ = lean_ctor_get(v_snd_2506_, 0);
v_snd_2514_ = lean_ctor_get(v_snd_2506_, 1);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_snd_2506_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2516_ = v_snd_2506_;
v_isShared_2517_ = v_isSharedCheck_2534_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_snd_2514_);
lean_inc(v_fst_2513_);
lean_dec(v_snd_2506_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2534_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_last_2519_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = lean_array_get_size(v_fst_2507_);
v___x_2531_ = lean_nat_dec_lt(v___x_2500_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
v_last_2519_ = v_fst_2513_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_array_fget_borrowed(v_fst_2507_, v___x_2500_);
lean_inc(v_snd_2514_);
lean_inc(v___x_2532_);
v___x_2533_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_2501_, v___x_2502_, v_fst_2513_, v___x_2532_, v_snd_2514_);
v_last_2519_ = v___x_2533_;
goto v___jp_2518_;
}
v___jp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2520_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_2499_, v_fst_2509_, v_fst_2507_, v_snd_2508_);
v___x_2521_ = lean_unsigned_to_nat(1u);
v___x_2522_ = lean_nat_add(v_snd_2514_, v___x_2521_);
lean_dec(v_snd_2514_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 1, v___x_2522_);
lean_ctor_set(v___x_2516_, 0, v_last_2519_);
v___x_2524_ = v___x_2516_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_last_2519_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2526_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 1, v___x_2524_);
lean_ctor_set(v___x_2511_, 0, v___x_2520_);
v___x_2526_ = v___x_2511_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0___boxed(lean_object* v_inst_2537_, lean_object* v___x_2538_, lean_object* v___x_2539_, lean_object* v___x_2540_, lean_object* v_a_2541_, lean_object* v_x_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0(v_inst_2537_, v___x_2538_, v___x_2539_, v___x_2540_, v_a_2541_, v_x_2542_, v___y_2543_);
lean_dec(v___x_2538_);
return v_res_2544_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1(lean_object* v_x1_2545_, lean_object* v_x2_2546_){
_start:
{
lean_object* v_snd_2547_; lean_object* v_snd_2548_; uint8_t v___x_2549_; 
v_snd_2547_ = lean_ctor_get(v_x1_2545_, 1);
v_snd_2548_ = lean_ctor_get(v_x2_2546_, 1);
v___x_2549_ = lean_nat_dec_lt(v_snd_2547_, v_snd_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1___boxed(lean_object* v_x1_2550_, lean_object* v_x2_2551_){
_start:
{
uint8_t v_res_2552_; lean_object* v_r_2553_; 
v_res_2552_ = l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__1(v_x1_2550_, v_x2_2551_);
lean_dec_ref(v_x2_2551_);
lean_dec_ref(v_x1_2550_);
v_r_2553_ = lean_box(v_res_2552_);
return v_r_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2(lean_object* v___x_2554_, lean_object* v___x_2555_, lean_object* v_fst_2556_, lean_object* v___x_2557_, lean_object* v_x_2558_){
_start:
{
lean_object* v_fst_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2573_; 
v_fst_2559_ = lean_ctor_get(v_x_2558_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_x_2558_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v_x_2558_, 1);
lean_dec(v_unused_2574_);
v___x_2561_ = v_x_2558_;
v_isShared_2562_ = v_isSharedCheck_2573_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_fst_2559_);
lean_dec(v_x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2573_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; 
lean_inc(v_fst_2559_);
v___x_2563_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2554_, v___x_2555_, v_fst_2556_, v_fst_2559_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2564_ = lean_mk_empty_array_with_capacity(v___x_2557_);
lean_inc_ref(v___x_2564_);
v___x_2565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 1, v___x_2565_);
v___x_2567_ = v___x_2561_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_fst_2559_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
else
{
lean_object* v_val_2569_; lean_object* v___x_2571_; 
v_val_2569_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_val_2569_);
lean_dec_ref_known(v___x_2563_, 1);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 1, v_val_2569_);
v___x_2571_ = v___x_2561_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_fst_2559_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_val_2569_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2___boxed(lean_object* v___x_2575_, lean_object* v___x_2576_, lean_object* v_fst_2577_, lean_object* v___x_2578_, lean_object* v_x_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2(v___x_2575_, v___x_2576_, v_fst_2577_, v___x_2578_, v_x_2579_);
lean_dec(v___x_2578_);
lean_dec(v_fst_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__3(lean_object* v_x1_2581_, lean_object* v_x2_2582_, lean_object* v_x3_2583_){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_x2_2582_);
lean_ctor_set(v___x_2584_, 1, v_x3_2583_);
v___x_2585_ = lean_array_push(v_x1_2581_, v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__4(lean_object* v___x_2586_, lean_object* v___f_2587_, lean_object* v_acc_2588_, lean_object* v_l_2589_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_2586_, v___f_2587_, v_acc_2588_, v_l_2589_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_2591_; lean_object* v_last_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v_last_2592_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg___closed__1);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v_last_2592_);
lean_ctor_set(v___x_2593_, 1, v___x_2591_);
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1(void){
_start:
{
lean_object* v___x_2594_; lean_object* v_d_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_obj_once(&l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0, &l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0_once, _init_l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__0);
v_d_2595_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_d_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf___redArg(lean_object* v_inst_2602_, lean_object* v_entries_2603_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___f_2608_; lean_object* v___x_2609_; size_t v_sz_2610_; size_t v___x_2611_; lean_object* v___x_2612_; lean_object* v_snd_2613_; lean_object* v_fst_2614_; lean_object* v_fst_2615_; lean_object* v_size_2616_; lean_object* v_buckets_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___y_2621_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2637_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2604_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0));
v___x_2605_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1));
v___x_2606_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v___x_2607_ = lean_unsigned_to_nat(0u);
v___f_2608_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2608_, 0, v_inst_2602_);
lean_closure_set(v___f_2608_, 1, v___x_2607_);
lean_closure_set(v___f_2608_, 2, v___x_2604_);
lean_closure_set(v___f_2608_, 3, v___x_2605_);
v___x_2609_ = lean_obj_once(&l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1, &l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__1);
v_sz_2610_ = lean_array_size(v_entries_2603_);
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2606_, v_entries_2603_, v___f_2608_, v_sz_2610_, v___x_2611_, v___x_2609_);
v_snd_2613_ = lean_ctor_get(v___x_2612_, 1);
v_fst_2614_ = lean_ctor_get(v_snd_2613_, 0);
lean_inc(v_fst_2614_);
v_fst_2615_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_fst_2615_);
lean_dec(v___x_2612_);
v_size_2616_ = lean_ctor_get(v_fst_2614_, 0);
lean_inc(v_size_2616_);
v_buckets_2617_ = lean_ctor_get(v_fst_2614_, 1);
lean_inc_ref(v_buckets_2617_);
lean_dec(v_fst_2614_);
v___f_2618_ = ((lean_object*)(l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__2));
v___f_2619_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_2619_, 0, v___x_2604_);
lean_closure_set(v___f_2619_, 1, v___x_2605_);
lean_closure_set(v___f_2619_, 2, v_fst_2615_);
lean_closure_set(v___f_2619_, 3, v___x_2607_);
v___x_2643_ = lean_mk_empty_array_with_capacity(v_size_2616_);
lean_dec(v_size_2616_);
v___x_2644_ = lean_array_get_size(v_buckets_2617_);
v___x_2645_ = lean_nat_dec_lt(v___x_2607_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_dec_ref(v_buckets_2617_);
v___y_2637_ = v___x_2643_;
goto v___jp_2636_;
}
else
{
lean_object* v___f_2646_; size_t v___x_2647_; lean_object* v___x_2648_; 
v___f_2646_ = ((lean_object*)(l_Lean_Meta_DiscrTree_moduleRootsOf___redArg___closed__4));
v___x_2647_ = lean_usize_of_nat(v___x_2644_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2606_, v___f_2646_, v_buckets_2617_, v___x_2611_, v___x_2647_, v___x_2643_);
v___y_2637_ = v___x_2648_;
goto v___jp_2636_;
}
v___jp_2620_:
{
size_t v_sz_2622_; lean_object* v___x_2623_; 
v_sz_2622_ = lean_array_size(v___y_2621_);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2606_, v___f_2619_, v_sz_2622_, v___x_2611_, v___y_2621_);
return v___x_2623_;
}
v___jp_2624_:
{
lean_object* v___x_2629_; 
v___x_2629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_2618_, v___y_2625_, v___y_2627_, v___y_2626_, v___y_2628_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2628_);
lean_dec(v___y_2625_);
v___y_2621_ = v___x_2629_;
goto v___jp_2620_;
}
v___jp_2630_:
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_nat_dec_le(v___y_2634_, v___y_2632_);
if (v___x_2635_ == 0)
{
lean_dec(v___y_2632_);
lean_inc(v___y_2634_);
v___y_2625_ = v___y_2631_;
v___y_2626_ = v___y_2634_;
v___y_2627_ = v___y_2633_;
v___y_2628_ = v___y_2634_;
goto v___jp_2624_;
}
else
{
v___y_2625_ = v___y_2631_;
v___y_2626_ = v___y_2634_;
v___y_2627_ = v___y_2633_;
v___y_2628_ = v___y_2632_;
goto v___jp_2624_;
}
}
v___jp_2636_:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = lean_array_get_size(v___y_2637_);
v___x_2639_ = lean_nat_dec_eq(v___x_2638_, v___x_2607_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2640_ = lean_unsigned_to_nat(1u);
v___x_2641_ = lean_nat_sub(v___x_2638_, v___x_2640_);
v___x_2642_ = lean_nat_dec_le(v___x_2607_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_inc(v___x_2641_);
v___y_2631_ = v___x_2638_;
v___y_2632_ = v___x_2641_;
v___y_2633_ = v___y_2637_;
v___y_2634_ = v___x_2641_;
goto v___jp_2630_;
}
else
{
v___y_2631_ = v___x_2638_;
v___y_2632_ = v___x_2641_;
v___y_2633_ = v___y_2637_;
v___y_2634_ = v___x_2607_;
goto v___jp_2630_;
}
}
else
{
v___y_2621_ = v___y_2637_;
goto v___jp_2620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_moduleRootsOf(lean_object* v_00_u03b1_2649_, lean_object* v_inst_2650_, lean_object* v_entries_2651_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Meta_DiscrTree_moduleRootsOf___redArg(v_inst_2650_, v_entries_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg___lam__0(lean_object* v_inst_2653_, lean_object* v___x_2654_, lean_object* v___x_2655_, lean_object* v_x1_2656_, lean_object* v_x2_2657_){
_start:
{
lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_fst_2658_ = lean_ctor_get(v_x2_2657_, 0);
lean_inc(v_fst_2658_);
v_snd_2659_ = lean_ctor_get(v_x2_2657_, 1);
lean_inc(v_snd_2659_);
lean_dec_ref(v_x2_2657_);
v___x_2660_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_mergeGroup___redArg(v_inst_2653_, v_snd_2659_);
v___x_2661_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2654_, v___x_2655_, v_x1_2656_, v_fst_2658_, v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg(lean_object* v_inst_2662_, lean_object* v_mods_2663_){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2664_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1, &l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_instInhabited___redArg___closed__1);
v___x_2665_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_groupByKey___redArg(v_mods_2663_);
v___x_2666_ = lean_unsigned_to_nat(0u);
v___x_2667_ = lean_array_get_size(v___x_2665_);
v___x_2668_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v___x_2669_ = lean_nat_dec_lt(v___x_2666_, v___x_2667_);
if (v___x_2669_ == 0)
{
lean_dec_ref(v___x_2665_);
lean_dec_ref(v_inst_2662_);
return v___x_2664_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___f_2672_; size_t v___x_2673_; size_t v___x_2674_; lean_object* v___x_2675_; 
v___x_2670_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0));
v___x_2671_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1));
v___f_2672_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_ofModuleRoots___redArg___lam__0), 5, 3);
lean_closure_set(v___f_2672_, 0, v_inst_2662_);
lean_closure_set(v___f_2672_, 1, v___x_2670_);
lean_closure_set(v___f_2672_, 2, v___x_2671_);
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = lean_usize_of_nat(v___x_2667_);
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2668_, v___f_2672_, v___x_2665_, v___x_2673_, v___x_2674_, v___x_2664_);
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___redArg___boxed(lean_object* v_inst_2676_, lean_object* v_mods_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Meta_DiscrTree_ofModuleRoots___redArg(v_inst_2676_, v_mods_2677_);
lean_dec_ref(v_mods_2677_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots(lean_object* v_00_u03b1_2679_, lean_object* v_inst_2680_, lean_object* v_mods_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Meta_DiscrTree_ofModuleRoots___redArg(v_inst_2680_, v_mods_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_ofModuleRoots___boxed(lean_object* v_00_u03b1_2683_, lean_object* v_inst_2684_, lean_object* v_mods_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Meta_DiscrTree_ofModuleRoots(v_00_u03b1_2683_, v_inst_2684_, v_mods_2685_);
lean_dec_ref(v_mods_2685_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___redArg(lean_object* v_inst_2687_, lean_object* v_d_2688_, lean_object* v_keys_2689_, lean_object* v_v_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_2687_, v_d_2688_, v_keys_2689_, v_v_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object* v_00_u03b1_2692_, lean_object* v_inst_2693_, lean_object* v_d_2694_, lean_object* v_keys_2695_, lean_object* v_v_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_2693_, v_d_2694_, v_keys_2695_, v_v_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(lean_object* v_as_2698_, lean_object* v_k_2699_, lean_object* v_x_2700_, lean_object* v_x_2701_){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v_m_2704_; lean_object* v_a_2705_; uint8_t v___x_2706_; 
v___x_2702_ = lean_nat_add(v_x_2700_, v_x_2701_);
v___x_2703_ = lean_unsigned_to_nat(1u);
v_m_2704_ = lean_nat_shiftr(v___x_2702_, v___x_2703_);
lean_dec(v___x_2702_);
v_a_2705_ = lean_array_fget_borrowed(v_as_2698_, v_m_2704_);
v___x_2706_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(v_a_2705_, v_k_2699_);
if (v___x_2706_ == 0)
{
uint8_t v___x_2707_; 
lean_dec(v_x_2701_);
v___x_2707_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(v_k_2699_, v_a_2705_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; 
lean_dec(v_m_2704_);
lean_dec(v_x_2700_);
lean_inc(v_a_2705_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_a_2705_);
return v___x_2708_;
}
else
{
lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_nat_dec_eq(v_m_2704_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; uint8_t v___x_2712_; 
v___x_2711_ = lean_nat_sub(v_m_2704_, v___x_2703_);
lean_dec(v_m_2704_);
v___x_2712_ = lean_nat_dec_lt(v___x_2711_, v_x_2700_);
if (v___x_2712_ == 0)
{
v_x_2701_ = v___x_2711_;
goto _start;
}
else
{
lean_object* v___x_2714_; 
lean_dec(v___x_2711_);
lean_dec(v_x_2700_);
v___x_2714_ = lean_box(0);
return v___x_2714_;
}
}
else
{
lean_object* v___x_2715_; 
lean_dec(v_m_2704_);
lean_dec(v_x_2700_);
v___x_2715_ = lean_box(0);
return v___x_2715_;
}
}
}
else
{
lean_object* v___x_2716_; uint8_t v___x_2717_; 
lean_dec(v_x_2700_);
v___x_2716_ = lean_nat_add(v_m_2704_, v___x_2703_);
lean_dec(v_m_2704_);
v___x_2717_ = lean_nat_dec_le(v___x_2716_, v_x_2701_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
lean_dec(v___x_2716_);
lean_dec(v_x_2701_);
v___x_2718_ = lean_box(0);
return v___x_2718_;
}
else
{
v_x_2700_ = v___x_2716_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg___boxed(lean_object* v_as_2720_, lean_object* v_k_2721_, lean_object* v_x_2722_, lean_object* v_x_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(v_as_2720_, v_k_2721_, v_x_2722_, v_x_2723_);
lean_dec_ref(v_k_2721_);
lean_dec_ref(v_as_2720_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(lean_object* v_keys_2725_, lean_object* v_i_2726_, lean_object* v_t_2727_){
_start:
{
lean_object* v_val_2731_; 
switch(lean_obj_tag(v_t_2727_))
{
case 2:
{
lean_object* v___x_2767_; 
v___x_2767_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_2727_);
v_val_2731_ = v___x_2767_;
goto v___jp_2730_;
}
case 3:
{
lean_object* v___x_2768_; 
v___x_2768_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg(v_t_2727_);
v_val_2731_ = v___x_2768_;
goto v___jp_2730_;
}
default: 
{
v_val_2731_ = v_t_2727_;
goto v___jp_2730_;
}
}
v___jp_2728_:
{
lean_object* v___x_2729_; 
v___x_2729_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
return v___x_2729_;
}
v___jp_2730_:
{
if (lean_obj_tag(v_val_2731_) == 0)
{
lean_object* v_key_2732_; lean_object* v_child_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v_key_2732_ = lean_ctor_get(v_val_2731_, 0);
lean_inc(v_key_2732_);
v_child_2733_ = lean_ctor_get(v_val_2731_, 1);
lean_inc_ref(v_child_2733_);
lean_dec_ref_known(v_val_2731_, 2);
v___x_2734_ = lean_array_get_size(v_keys_2725_);
v___x_2735_ = lean_nat_dec_lt(v_i_2726_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; 
lean_dec_ref(v_child_2733_);
lean_dec(v_key_2732_);
lean_dec(v_i_2726_);
v___x_2736_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
return v___x_2736_;
}
else
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = lean_array_fget_borrowed(v_keys_2725_, v_i_2726_);
v___x_2738_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_2737_, v_key_2732_);
lean_dec(v_key_2732_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; 
lean_dec_ref(v_child_2733_);
lean_dec(v_i_2726_);
v___x_2739_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = lean_unsigned_to_nat(1u);
v___x_2741_ = lean_nat_add(v_i_2726_, v___x_2740_);
lean_dec(v_i_2726_);
v_i_2726_ = v___x_2741_;
v_t_2727_ = v_child_2733_;
goto _start;
}
}
}
else
{
lean_object* v_vs_2743_; lean_object* v_children_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2766_; 
v_vs_2743_ = lean_ctor_get(v_val_2731_, 0);
v_children_2744_ = lean_ctor_get(v_val_2731_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_val_2731_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2746_ = v_val_2731_;
v_isShared_2747_ = v_isSharedCheck_2766_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_children_2744_);
lean_inc(v_vs_2743_);
lean_dec(v_val_2731_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2766_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2748_ = lean_array_get_size(v_keys_2725_);
v___x_2749_ = lean_nat_dec_lt(v_i_2726_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_del_object(v___x_2746_);
lean_dec_ref(v_children_2744_);
lean_dec(v_i_2726_);
return v_vs_2743_;
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
lean_dec_ref(v_vs_2743_);
v___x_2750_ = lean_unsigned_to_nat(0u);
v___x_2751_ = lean_array_get_size(v_children_2744_);
v___x_2752_ = lean_nat_dec_lt(v___x_2750_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_del_object(v___x_2746_);
lean_dec_ref(v_children_2744_);
lean_dec(v_i_2726_);
goto v___jp_2728_;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2753_ = lean_unsigned_to_nat(1u);
v___x_2754_ = lean_nat_sub(v___x_2751_, v___x_2753_);
v___x_2755_ = lean_nat_dec_le(v___x_2750_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_dec(v___x_2754_);
lean_del_object(v___x_2746_);
lean_dec_ref(v_children_2744_);
lean_dec(v_i_2726_);
goto v___jp_2728_;
}
else
{
lean_object* v_k_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v_k_2756_ = lean_array_fget_borrowed(v_keys_2725_, v_i_2726_);
v___x_2757_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__1));
lean_inc(v_k_2756_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set_tag(v___x_2746_, 0);
lean_ctor_set(v___x_2746_, 1, v___x_2757_);
lean_ctor_set(v___x_2746_, 0, v_k_2756_);
v___x_2759_ = v___x_2746_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_k_2756_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(v_children_2744_, v___x_2759_, v___x_2750_, v___x_2754_);
lean_dec_ref(v___x_2759_);
lean_dec_ref(v_children_2744_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_dec(v_i_2726_);
goto v___jp_2728_;
}
else
{
lean_object* v_val_2761_; lean_object* v_snd_2762_; lean_object* v___x_2763_; 
v_val_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v_snd_2762_ = lean_ctor_get(v_val_2761_, 1);
lean_inc(v_snd_2762_);
lean_dec(v_val_2761_);
v___x_2763_ = lean_nat_add(v_i_2726_, v___x_2753_);
lean_dec(v_i_2726_);
v_i_2726_ = v___x_2763_;
v_t_2727_ = v_snd_2762_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg___boxed(lean_object* v_keys_2769_, lean_object* v_i_2770_, lean_object* v_t_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(v_keys_2769_, v_i_2770_, v_t_2771_);
lean_dec_ref(v_keys_2769_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux(lean_object* v_00_u03b1_2773_, lean_object* v_keys_2774_, lean_object* v_i_2775_, lean_object* v_t_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(v_keys_2774_, v_i_2775_, v_t_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_keys_2779_, lean_object* v_i_2780_, lean_object* v_t_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux(v_00_u03b1_2778_, v_keys_2779_, v_i_2780_, v_t_2781_);
lean_dec_ref(v_keys_2779_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0(lean_object* v_00_u03b1_2783_, lean_object* v_as_2784_, lean_object* v_k_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___redArg(v_as_2784_, v_k_2785_, v_x_2786_, v_x_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0___boxed(lean_object* v_00_u03b1_2790_, lean_object* v_as_2791_, lean_object* v_k_2792_, lean_object* v_x_2793_, lean_object* v_x_2794_, lean_object* v_x_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_spec__0(v_00_u03b1_2790_, v_as_2791_, v_k_2792_, v_x_2793_, v_x_2794_, v_x_2795_);
lean_dec_ref(v_k_2792_);
lean_dec_ref(v_as_2791_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_match__1_splitter___redArg(lean_object* v_x_2797_, lean_object* v_h__1_2798_, lean_object* v_h__2_2799_){
_start:
{
if (lean_obj_tag(v_x_2797_) == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec(v_h__2_2799_);
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_apply_1(v_h__1_2798_, v___x_2800_);
return v___x_2801_;
}
else
{
lean_object* v_val_2802_; lean_object* v_fst_2803_; lean_object* v_snd_2804_; lean_object* v___x_2805_; 
lean_dec(v_h__1_2798_);
v_val_2802_ = lean_ctor_get(v_x_2797_, 0);
lean_inc(v_val_2802_);
lean_dec_ref_known(v_x_2797_, 1);
v_fst_2803_ = lean_ctor_get(v_val_2802_, 0);
lean_inc(v_fst_2803_);
v_snd_2804_ = lean_ctor_get(v_val_2802_, 1);
lean_inc(v_snd_2804_);
lean_dec(v_val_2802_);
v___x_2805_ = lean_apply_2(v_h__2_2799_, v_fst_2803_, v_snd_2804_);
return v___x_2805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux_match__1_splitter(lean_object* v_00_u03b1_2806_, lean_object* v_motive_2807_, lean_object* v_x_2808_, lean_object* v_h__1_2809_, lean_object* v_h__2_2810_){
_start:
{
if (lean_obj_tag(v_x_2808_) == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec(v_h__2_2810_);
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_apply_1(v_h__1_2809_, v___x_2811_);
return v___x_2812_;
}
else
{
lean_object* v_val_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___x_2816_; 
lean_dec(v_h__1_2809_);
v_val_2813_ = lean_ctor_get(v_x_2808_, 0);
lean_inc(v_val_2813_);
lean_dec_ref_known(v_x_2808_, 1);
v_fst_2814_ = lean_ctor_get(v_val_2813_, 0);
lean_inc(v_fst_2814_);
v_snd_2815_ = lean_ctor_get(v_val_2813_, 1);
lean_inc(v_snd_2815_);
lean_dec(v_val_2813_);
v___x_2816_ = lean_apply_2(v_h__2_2810_, v_fst_2814_, v_snd_2815_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1___redArg(lean_object* v_msg_2817_){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0, &l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_unfold_spec__0___redArg___closed__0);
v___x_2819_ = lean_panic_fn_borrowed(v___x_2818_, v_msg_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1(lean_object* v_00_u03b1_2820_, lean_object* v_msg_2821_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1___redArg(v_msg_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2823_, lean_object* v_vals_2824_, lean_object* v_i_2825_, lean_object* v_k_2826_){
_start:
{
lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2827_ = lean_array_get_size(v_keys_2823_);
v___x_2828_ = lean_nat_dec_lt(v_i_2825_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; 
lean_dec(v_i_2825_);
v___x_2829_ = lean_box(0);
return v___x_2829_;
}
else
{
lean_object* v_k_x27_2830_; uint8_t v___x_2831_; 
v_k_x27_2830_ = lean_array_fget_borrowed(v_keys_2823_, v_i_2825_);
v___x_2831_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_2826_, v_k_x27_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_unsigned_to_nat(1u);
v___x_2833_ = lean_nat_add(v_i_2825_, v___x_2832_);
lean_dec(v_i_2825_);
v_i_2825_ = v___x_2833_;
goto _start;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_array_fget_borrowed(v_vals_2824_, v_i_2825_);
lean_dec(v_i_2825_);
lean_inc(v___x_2835_);
v___x_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
return v___x_2836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2837_, lean_object* v_vals_2838_, lean_object* v_i_2839_, lean_object* v_k_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(v_keys_2837_, v_vals_2838_, v_i_2839_, v_k_2840_);
lean_dec(v_k_2840_);
lean_dec_ref(v_vals_2838_);
lean_dec_ref(v_keys_2837_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(lean_object* v_x_2842_, size_t v_x_2843_, lean_object* v_x_2844_){
_start:
{
if (lean_obj_tag(v_x_2842_) == 0)
{
lean_object* v_es_2845_; lean_object* v___x_2846_; size_t v___x_2847_; size_t v___x_2848_; lean_object* v_j_2849_; lean_object* v___x_2850_; 
v_es_2845_ = lean_ctor_get(v_x_2842_, 0);
v___x_2846_ = lean_box(2);
v___x_2847_ = ((size_t)31ULL);
v___x_2848_ = lean_usize_land(v_x_2843_, v___x_2847_);
v_j_2849_ = lean_usize_to_nat(v___x_2848_);
v___x_2850_ = lean_array_get_borrowed(v___x_2846_, v_es_2845_, v_j_2849_);
lean_dec(v_j_2849_);
switch(lean_obj_tag(v___x_2850_))
{
case 0:
{
lean_object* v_key_2851_; lean_object* v_val_2852_; uint8_t v___x_2853_; 
v_key_2851_ = lean_ctor_get(v___x_2850_, 0);
v_val_2852_ = lean_ctor_get(v___x_2850_, 1);
v___x_2853_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2844_, v_key_2851_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_box(0);
return v___x_2854_;
}
else
{
lean_object* v___x_2855_; 
lean_inc(v_val_2852_);
v___x_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_val_2852_);
return v___x_2855_;
}
}
case 1:
{
lean_object* v_node_2856_; size_t v___x_2857_; size_t v___x_2858_; 
v_node_2856_ = lean_ctor_get(v___x_2850_, 0);
v___x_2857_ = ((size_t)5ULL);
v___x_2858_ = lean_usize_shift_right(v_x_2843_, v___x_2857_);
v_x_2842_ = v_node_2856_;
v_x_2843_ = v___x_2858_;
goto _start;
}
default: 
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_box(0);
return v___x_2860_;
}
}
}
else
{
lean_object* v_ks_2861_; lean_object* v_vs_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_ks_2861_ = lean_ctor_get(v_x_2842_, 0);
v_vs_2862_ = lean_ctor_get(v_x_2842_, 1);
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(v_ks_2861_, v_vs_2862_, v___x_2863_, v_x_2844_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg___boxed(lean_object* v_x_2865_, lean_object* v_x_2866_, lean_object* v_x_2867_){
_start:
{
size_t v_x_233__boxed_2868_; lean_object* v_res_2869_; 
v_x_233__boxed_2868_ = lean_unbox_usize(v_x_2866_);
lean_dec(v_x_2866_);
v_res_2869_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(v_x_2865_, v_x_233__boxed_2868_, v_x_2867_);
lean_dec(v_x_2867_);
lean_dec_ref(v_x_2865_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(lean_object* v_x_2870_, lean_object* v_x_2871_){
_start:
{
uint64_t v___x_2872_; size_t v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2871_);
v___x_2873_ = lean_uint64_to_usize(v___x_2872_);
v___x_2874_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(v_x_2870_, v___x_2873_, v_x_2871_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg___boxed(lean_object* v_x_2875_, lean_object* v_x_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(v_x_2875_, v_x_2876_);
lean_dec(v_x_2876_);
lean_dec_ref(v_x_2875_);
return v_res_2877_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2879_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3));
v___x_2880_ = lean_unsigned_to_nat(23u);
v___x_2881_ = lean_unsigned_to_nat(385u);
v___x_2882_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__0));
v___x_2883_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow___redArg___closed__0));
v___x_2884_ = l_mkPanicMessageWithDecl(v___x_2883_, v___x_2882_, v___x_2881_, v___x_2880_, v___x_2879_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg(lean_object* v_d_2885_, lean_object* v_keys_2886_){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = lean_array_get_size(v_keys_2886_);
v___x_2888_ = lean_unsigned_to_nat(0u);
v___x_2889_ = lean_nat_dec_eq(v___x_2887_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; lean_object* v_k_2891_; lean_object* v___x_2892_; 
v___x_2890_ = lean_box(0);
v_k_2891_ = lean_array_get_borrowed(v___x_2890_, v_keys_2886_, v___x_2888_);
v___x_2892_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(v_d_2885_, v_k_2891_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2893_; 
v___x_2893_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg___closed__0));
return v___x_2893_;
}
else
{
lean_object* v_val_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_val_2894_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_val_2894_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_getEntriesWithKeysAux___redArg(v_keys_2886_, v___x_2895_, v_val_2894_);
return v___x_2896_;
}
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_obj_once(&l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1, &l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1_once, _init_l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___closed__1);
v___x_2898_ = l_panic___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__1___redArg(v___x_2897_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg___boxed(lean_object* v_d_2899_, lean_object* v_keys_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg(v_d_2899_, v_keys_2900_);
lean_dec_ref(v_keys_2900_);
lean_dec_ref(v_d_2899_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys(lean_object* v_00_u03b1_2902_, lean_object* v_d_2903_, lean_object* v_keys_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Meta_DiscrTree_getEntriesWithKeys___redArg(v_d_2903_, v_keys_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getEntriesWithKeys___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_d_2907_, lean_object* v_keys_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Meta_DiscrTree_getEntriesWithKeys(v_00_u03b1_2906_, v_d_2907_, v_keys_2908_);
lean_dec_ref(v_keys_2908_);
lean_dec_ref(v_d_2907_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0(lean_object* v_00_u03b2_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___redArg(v_x_2911_, v_x_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0___boxed(lean_object* v_00_u03b2_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0(v_00_u03b2_2914_, v_x_2915_, v_x_2916_);
lean_dec(v_x_2916_);
lean_dec_ref(v_x_2915_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0(lean_object* v_00_u03b2_2918_, lean_object* v_x_2919_, size_t v_x_2920_, lean_object* v_x_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___redArg(v_x_2919_, v_x_2920_, v_x_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2923_, lean_object* v_x_2924_, lean_object* v_x_2925_, lean_object* v_x_2926_){
_start:
{
size_t v_x_349__boxed_2927_; lean_object* v_res_2928_; 
v_x_349__boxed_2927_ = lean_unbox_usize(v_x_2925_);
lean_dec(v_x_2925_);
v_res_2928_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0(v_00_u03b2_2923_, v_x_2924_, v_x_349__boxed_2927_, v_x_2926_);
lean_dec(v_x_2926_);
lean_dec_ref(v_x_2924_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2929_, lean_object* v_keys_2930_, lean_object* v_vals_2931_, lean_object* v_heq_2932_, lean_object* v_i_2933_, lean_object* v_k_2934_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___redArg(v_keys_2930_, v_vals_2931_, v_i_2933_, v_k_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2936_, lean_object* v_keys_2937_, lean_object* v_vals_2938_, lean_object* v_heq_2939_, lean_object* v_i_2940_, lean_object* v_k_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_getEntriesWithKeys_spec__0_spec__0_spec__2(v_00_u03b2_2936_, v_keys_2937_, v_vals_2938_, v_heq_2939_, v_i_2940_, v_k_2941_);
lean_dec(v_k_2941_);
lean_dec_ref(v_vals_2938_);
lean_dec_ref(v_keys_2937_);
return v_res_2942_;
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
