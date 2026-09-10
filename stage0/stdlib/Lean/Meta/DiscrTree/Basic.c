// Lean compiler output
// Module: Lean.Meta.DiscrTree.Basic
// Imports: public import Lean.Meta.DiscrTree.Types public import Lean.CoreM import Init.Data.Range.Polymorphic.Iterators import Init.Omega
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_join(lean_object*);
lean_object* l_List_format___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_binInsertM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "noindex"};
static const lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 166, 27, 47, 207, 202, 99, 39)}};
static const lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_mkNoindexAnnotation___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_hasNoindexAnnotation___boxed(lean_object*);
static const lean_array_object l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_value),((lean_object*)&l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
static lean_once_cell_t l_Lean_Meta_DiscrTree_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instInhabited___closed__0;
static lean_once_cell_t l_Lean_Meta_DiscrTree_instInhabited___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_instInhabited___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
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
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "node"};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5_value;
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5;
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
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__7_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__2_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__3_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__4_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__8_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Key_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object* v_00_u03b1_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1));
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___closed__0, &l_Lean_Meta_DiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_DiscrTree_instInhabited___closed__0);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object* v_00_u03b1_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___closed__1, &l_Lean_Meta_DiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_DiscrTree_instInhabited___closed__1);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_empty(lean_object* v_00_u03b1_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instInhabited___closed__1, &l_Lean_Meta_DiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_DiscrTree_instInhabited___closed__1);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_box(0);
v___x_40_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__5));
v___x_41_ = l_Lean_mkConst(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_box(0);
v___x_50_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__8));
v___x_51_ = l_Lean_mkConst(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_box(0);
v___x_60_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__11));
v___x_61_ = l_Lean_mkConst(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_box(0);
v___x_69_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__15));
v___x_70_ = l_Lean_mkConst(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_box(0);
v___x_77_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__18));
v___x_78_ = l_Lean_mkConst(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_box(0);
v___x_87_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__21));
v___x_88_ = l_Lean_mkConst(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_box(0);
v___x_96_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__25));
v___x_97_ = l_Lean_mkConst(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_box(0);
v___x_106_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__28));
v___x_107_ = l_Lean_mkConst(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_box(0);
v___x_116_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__31));
v___x_117_ = l_Lean_mkConst(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_box(0);
v___x_126_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__34));
v___x_127_ = l_Lean_mkConst(v___x_126_, v___x_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0(lean_object* v_k_128_){
_start:
{
switch(lean_obj_tag(v_k_128_))
{
case 0:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__6);
return v___x_129_;
}
case 1:
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__9);
return v___x_130_;
}
case 2:
{
lean_object* v_a_131_; lean_object* v___x_132_; 
v_a_131_ = lean_ctor_get(v_k_128_, 0);
lean_inc_ref(v_a_131_);
lean_dec_ref_known(v_k_128_, 1);
v___x_132_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__12);
if (lean_obj_tag(v_a_131_) == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__16);
v___x_134_ = l_Lean_Expr_lit___override(v_a_131_);
v___x_135_ = l_Lean_Expr_app___override(v___x_133_, v___x_134_);
v___x_136_ = l_Lean_Expr_app___override(v___x_132_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__19);
v___x_138_ = l_Lean_Expr_lit___override(v_a_131_);
v___x_139_ = l_Lean_Expr_app___override(v___x_137_, v___x_138_);
v___x_140_ = l_Lean_Expr_app___override(v___x_132_, v___x_139_);
return v___x_140_;
}
}
case 3:
{
lean_object* v_a_141_; lean_object* v_a_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_a_141_ = lean_ctor_get(v_k_128_, 0);
lean_inc(v_a_141_);
v_a_142_ = lean_ctor_get(v_k_128_, 1);
lean_inc(v_a_142_);
lean_dec_ref_known(v_k_128_, 2);
v___x_143_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__22);
v___x_144_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__26);
v___x_145_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_141_);
v___x_146_ = l_Lean_Expr_app___override(v___x_144_, v___x_145_);
v___x_147_ = l_Lean_mkNatLit(v_a_142_);
v___x_148_ = l_Lean_mkAppB(v___x_143_, v___x_146_, v___x_147_);
return v___x_148_;
}
case 4:
{
lean_object* v_a_149_; lean_object* v_a_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_a_149_ = lean_ctor_get(v_k_128_, 0);
lean_inc(v_a_149_);
v_a_150_ = lean_ctor_get(v_k_128_, 1);
lean_inc(v_a_150_);
lean_dec_ref_known(v_k_128_, 2);
v___x_151_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__29);
v___x_152_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_149_);
v___x_153_ = l_Lean_mkNatLit(v_a_150_);
v___x_154_ = l_Lean_mkAppB(v___x_151_, v___x_152_, v___x_153_);
return v___x_154_;
}
case 5:
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__32);
return v___x_155_;
}
default: 
{
lean_object* v_a_156_; lean_object* v_a_157_; lean_object* v_a_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_a_156_ = lean_ctor_get(v_k_128_, 0);
lean_inc(v_a_156_);
v_a_157_ = lean_ctor_get(v_k_128_, 1);
lean_inc(v_a_157_);
v_a_158_ = lean_ctor_get(v_k_128_, 2);
lean_inc(v_a_158_);
lean_dec_ref_known(v_k_128_, 3);
v___x_159_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35, &l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___lam__0___closed__35);
v___x_160_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_156_);
v___x_161_ = l_Lean_mkNatLit(v_a_157_);
v___x_162_ = l_Lean_mkNatLit(v_a_158_);
v___x_163_ = l_Lean_mkApp3(v___x_159_, v___x_160_, v___x_161_, v___x_162_);
return v___x_163_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_box(0);
v___x_171_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___closed__1));
v___x_172_ = l_Lean_mkConst(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__3(void){
_start:
{
lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___closed__2, &l_Lean_Meta_DiscrTree_instToExprKey___closed__2_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__2);
v___f_174_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instToExprKey___closed__0));
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___f_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Lean_Meta_DiscrTree_instToExprKey___closed__3, &l_Lean_Meta_DiscrTree_instToExprKey___closed__3_once, _init_l_Lean_Meta_DiscrTree_instToExprKey___closed__3);
return v___x_176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_k_u2081_180_; lean_object* v_k_u2082_181_; 
switch(lean_obj_tag(v_x_177_))
{
case 2:
{
if (lean_obj_tag(v_x_178_) == 2)
{
lean_object* v_a_185_; lean_object* v_a_186_; uint8_t v___x_187_; 
v_a_185_ = lean_ctor_get(v_x_177_, 0);
v_a_186_ = lean_ctor_get(v_x_178_, 0);
v___x_187_ = l_Lean_Literal_lt(v_a_185_, v_a_186_);
return v___x_187_;
}
else
{
v_k_u2081_180_ = v_x_177_;
v_k_u2082_181_ = v_x_178_;
goto v___jp_179_;
}
}
case 3:
{
if (lean_obj_tag(v_x_178_) == 3)
{
lean_object* v_a_188_; lean_object* v_a_189_; lean_object* v_a_190_; lean_object* v_a_191_; uint8_t v___x_192_; 
v_a_188_ = lean_ctor_get(v_x_177_, 0);
v_a_189_ = lean_ctor_get(v_x_177_, 1);
v_a_190_ = lean_ctor_get(v_x_178_, 0);
v_a_191_ = lean_ctor_get(v_x_178_, 1);
v___x_192_ = l_Lean_Name_quickLt(v_a_188_, v_a_190_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_instBEqFVarId_beq(v_a_188_, v_a_190_);
if (v___x_193_ == 0)
{
return v___x_193_;
}
else
{
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_lt(v_a_189_, v_a_191_);
return v___x_194_;
}
}
else
{
return v___x_192_;
}
}
else
{
v_k_u2081_180_ = v_x_177_;
v_k_u2082_181_ = v_x_178_;
goto v___jp_179_;
}
}
case 4:
{
if (lean_obj_tag(v_x_178_) == 4)
{
lean_object* v_a_195_; lean_object* v_a_196_; lean_object* v_a_197_; lean_object* v_a_198_; uint8_t v___x_199_; 
v_a_195_ = lean_ctor_get(v_x_177_, 0);
v_a_196_ = lean_ctor_get(v_x_177_, 1);
v_a_197_ = lean_ctor_get(v_x_178_, 0);
v_a_198_ = lean_ctor_get(v_x_178_, 1);
v___x_199_ = l_Lean_Name_quickLt(v_a_195_, v_a_197_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = lean_name_eq(v_a_195_, v_a_197_);
if (v___x_200_ == 0)
{
return v___x_200_;
}
else
{
uint8_t v___x_201_; 
v___x_201_ = lean_nat_dec_lt(v_a_196_, v_a_198_);
return v___x_201_;
}
}
else
{
return v___x_199_;
}
}
else
{
v_k_u2081_180_ = v_x_177_;
v_k_u2082_181_ = v_x_178_;
goto v___jp_179_;
}
}
case 6:
{
if (lean_obj_tag(v_x_178_) == 6)
{
lean_object* v_a_202_; lean_object* v_a_203_; lean_object* v_a_204_; lean_object* v_a_205_; lean_object* v_a_206_; lean_object* v_a_207_; uint8_t v___x_208_; uint8_t v___y_210_; uint8_t v___x_213_; 
v_a_202_ = lean_ctor_get(v_x_177_, 0);
v_a_203_ = lean_ctor_get(v_x_177_, 1);
v_a_204_ = lean_ctor_get(v_x_177_, 2);
v_a_205_ = lean_ctor_get(v_x_178_, 0);
v_a_206_ = lean_ctor_get(v_x_178_, 1);
v_a_207_ = lean_ctor_get(v_x_178_, 2);
v___x_208_ = lean_nat_dec_lt(v_a_204_, v_a_207_);
v___x_213_ = l_Lean_Name_quickLt(v_a_202_, v_a_205_);
if (v___x_213_ == 0)
{
uint8_t v___x_214_; 
v___x_214_ = lean_name_eq(v_a_202_, v_a_205_);
if (v___x_214_ == 0)
{
v___y_210_ = v___x_214_;
goto v___jp_209_;
}
else
{
uint8_t v___x_215_; 
v___x_215_ = lean_nat_dec_lt(v_a_203_, v_a_206_);
v___y_210_ = v___x_215_;
goto v___jp_209_;
}
}
else
{
v___y_210_ = v___x_213_;
goto v___jp_209_;
}
v___jp_209_:
{
if (v___y_210_ == 0)
{
uint8_t v___x_211_; 
v___x_211_ = lean_name_eq(v_a_202_, v_a_205_);
if (v___x_211_ == 0)
{
if (v___x_211_ == 0)
{
return v___x_211_;
}
else
{
return v___x_208_;
}
}
else
{
uint8_t v___x_212_; 
v___x_212_ = lean_nat_dec_eq(v_a_203_, v_a_206_);
if (v___x_212_ == 0)
{
return v___x_212_;
}
else
{
return v___x_208_;
}
}
}
else
{
return v___y_210_;
}
}
}
else
{
v_k_u2081_180_ = v_x_177_;
v_k_u2082_181_ = v_x_178_;
goto v___jp_179_;
}
}
default: 
{
v_k_u2081_180_ = v_x_177_;
v_k_u2082_181_ = v_x_178_;
goto v___jp_179_;
}
}
v___jp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = l_Lean_Meta_DiscrTree_Key_ctorIdx(v_k_u2081_180_);
v___x_183_ = l_Lean_Meta_DiscrTree_Key_ctorIdx(v_k_u2082_181_);
v___x_184_ = lean_nat_dec_lt(v___x_182_, v___x_183_);
lean_dec(v___x_183_);
lean_dec(v___x_182_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_lt___boxed(lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_Meta_DiscrTree_Key_lt(v_x_216_, v_x_217_);
lean_dec(v_x_217_);
lean_dec(v_x_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instLTKey(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_box(0);
return v___x_220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_instDecidableLtKey(lean_object* v_a_221_, lean_object* v_b_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_Meta_DiscrTree_Key_lt(v_a_221_, v_b_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instDecidableLtKey___boxed(lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Lean_Meta_DiscrTree_instDecidableLtKey(v_a_224_, v_b_225_);
lean_dec(v_b_225_);
lean_dec(v_a_224_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_format(lean_object* v_x_240_){
_start:
{
switch(lean_obj_tag(v_x_240_))
{
case 0:
{
lean_object* v___x_241_; 
v___x_241_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__1));
return v___x_241_;
}
case 1:
{
lean_object* v___x_242_; 
v___x_242_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__3));
return v___x_242_;
}
case 2:
{
lean_object* v_a_243_; 
v_a_243_ = lean_ctor_get(v_x_240_, 0);
lean_inc_ref(v_a_243_);
lean_dec_ref_known(v_x_240_, 1);
if (lean_obj_tag(v_a_243_) == 0)
{
lean_object* v_val_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_val_244_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_252_ == 0)
{
v___x_246_ = v_a_243_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_val_244_);
lean_dec(v_a_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = l_Nat_reprFast(v_val_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 3);
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_object* v_val_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_val_253_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v_a_243_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_val_253_);
lean_dec(v_a_243_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = l_String_quote(v_val_253_);
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 3);
lean_ctor_set(v___x_255_, 0, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
case 5:
{
lean_object* v___x_262_; 
v___x_262_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__5));
return v___x_262_;
}
case 6:
{
lean_object* v_a_263_; lean_object* v_a_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_a_263_ = lean_ctor_get(v_x_240_, 0);
lean_inc(v_a_263_);
v_a_264_ = lean_ctor_get(v_x_240_, 1);
lean_inc(v_a_264_);
lean_dec_ref_known(v_x_240_, 3);
v___x_265_ = 1;
v___x_266_ = l_Lean_Name_toString(v_a_263_, v___x_265_);
v___x_267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
v___x_268_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__7));
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Nat_reprFast(v_a_264_);
v___x_271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_269_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
return v___x_272_;
}
default: 
{
lean_object* v_a_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_a_273_ = lean_ctor_get(v_x_240_, 0);
lean_inc(v_a_273_);
lean_dec(v_x_240_);
v___x_274_ = 1;
v___x_275_ = l_Lean_Name_toString(v_a_273_, v___x_274_);
v___x_276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__2));
v___x_285_ = lean_string_length(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__4);
v___x_287_ = lean_nat_to_int(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg(lean_object* v_inst_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_vs_303_; lean_object* v_children_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_339_; 
v_vs_303_ = lean_ctor_get(v_x_302_, 0);
v_children_304_ = lean_ctor_get(v_x_302_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_339_ == 0)
{
v___x_306_ = v_x_302_;
v_isShared_307_ = v_isSharedCheck_339_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_children_304_);
lean_inc(v_vs_303_);
lean_dec(v_x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_339_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___y_311_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
lean_inc_ref(v_inst_301_);
v___f_308_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0), 2, 1);
lean_closure_set(v___f_308_, 0, v_inst_301_);
v___x_309_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__1));
v___x_329_ = lean_array_get_size(v_vs_303_);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_nat_dec_eq(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_332_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__3));
v___x_333_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___closed__5));
v___x_334_ = lean_array_to_list(v_vs_303_);
v___x_335_ = l_List_format___redArg(v_inst_301_, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_333_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_332_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___y_311_ = v___x_337_;
goto v___jp_310_;
}
else
{
lean_object* v___x_338_; 
lean_dec_ref(v_vs_303_);
lean_dec_ref(v_inst_301_);
v___x_338_ = lean_box(0);
v___y_311_ = v___x_338_;
goto v___jp_310_;
}
v___jp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 5);
lean_ctor_set(v___x_306_, 1, v___y_311_);
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_313_ = v___x_306_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___y_311_);
v___x_313_ = v_reuseFailAlloc_328_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_314_ = lean_array_to_list(v_children_304_);
v___x_315_ = lean_box(0);
v___x_316_ = l_List_mapTR_loop___redArg(v___f_308_, v___x_314_, v___x_315_);
v___x_317_ = l_Std_Format_join(v___x_316_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_313_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5);
v___x_320_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6));
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_318_);
v___x_322_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7));
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_319_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = 0;
v___x_326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v___x_325_);
v___x_327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_325_);
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0(lean_object* v_inst_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_364_; 
v_fst_342_ = lean_ctor_get(v_x_341_, 0);
v_snd_343_ = lean_ctor_get(v_x_341_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_364_ == 0)
{
v___x_345_ = v_x_341_;
v_isShared_346_ = v_isSharedCheck_364_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_snd_343_);
lean_inc(v_fst_342_);
lean_dec(v_x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_364_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_347_ = lean_box(1);
v___x_348_ = l_Lean_Meta_DiscrTree_Key_format(v_fst_342_);
v___x_349_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1));
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 5);
lean_ctor_set(v___x_345_, 1, v___x_349_);
lean_ctor_set(v___x_345_, 0, v___x_348_);
v___x_351_ = v___x_345_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_363_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_352_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_340_, v_snd_343_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5);
v___x_355_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6));
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_353_);
v___x_357_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7));
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_354_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = 0;
v___x_361_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*1, v___x_360_);
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_347_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_format(lean_object* v_00_u03b1_365_, lean_object* v_inst_366_, lean_object* v_x_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_366_, v_x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie___redArg(lean_object* v_inst_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format), 3, 2);
lean_closure_set(v___x_370_, 0, lean_box(0));
lean_closure_set(v___x_370_, 1, v_inst_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormatTrie(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_format), 3, 2);
lean_closure_set(v___x_373_, 0, lean_box(0));
lean_closure_set(v___x_373_, 1, v_inst_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___redArg___lam__0(lean_object* v_inst_374_, lean_object* v_p_375_, lean_object* v_k_376_, lean_object* v_c_377_){
_start:
{
lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_408_; 
v_fst_378_ = lean_ctor_get(v_p_375_, 0);
v_snd_379_ = lean_ctor_get(v_p_375_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_p_375_);
if (v_isSharedCheck_408_ == 0)
{
v___x_381_ = v_p_375_;
v_isShared_382_ = v_isSharedCheck_408_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snd_379_);
lean_inc(v_fst_378_);
lean_dec(v_p_375_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_408_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint8_t v___x_383_; lean_object* v___y_385_; uint8_t v___x_405_; 
v___x_383_ = 0;
v___x_405_ = lean_unbox(v_fst_378_);
lean_dec(v_fst_378_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_box(1);
v___y_385_ = v___x_406_;
goto v___jp_384_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
v___y_385_ = v___x_407_;
goto v___jp_384_;
}
v___jp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
lean_inc(v___y_385_);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v_snd_379_);
lean_ctor_set(v___x_386_, 1, v___y_385_);
v___x_387_ = l_Lean_Meta_DiscrTree_Key_format(v_k_376_);
v___x_388_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__1));
v___x_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_Meta_DiscrTree_Trie_format___redArg(v_inst_374_, v_c_377_);
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_obj_once(&l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5, &l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5_once, _init_l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__5);
v___x_393_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__6));
v___x_394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_391_);
v___x_395_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_format___redArg___lam__0___closed__7));
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_392_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = 0;
v___x_399_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*1, v___x_398_);
v___x_400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_386_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_box(v___x_383_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___x_400_);
lean_ctor_set(v___x_381_, 0, v___x_401_);
v___x_403_ = v___x_381_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_400_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format___redArg(lean_object* v_inst_413_, lean_object* v_d_414_){
_start:
{
lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_snd_418_; uint8_t v___x_419_; lean_object* v___x_420_; 
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format___redArg___lam__0), 4, 1);
lean_closure_set(v___f_415_, 0, v_inst_413_);
v___x_416_ = ((lean_object*)(l_Lean_Meta_DiscrTree_format___redArg___closed__0));
v___x_417_ = l_Lean_PersistentHashMap_foldl___redArg(v_d_414_, v___f_415_, v___x_416_);
v_snd_418_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_snd_418_);
lean_dec(v___x_417_);
v___x_419_ = 0;
v___x_420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_420_, 0, v_snd_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_format(lean_object* v_00_u03b1_421_, lean_object* v_inst_422_, lean_object* v_d_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_DiscrTree_format___redArg(v_inst_422_, v_d_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormat___redArg(lean_object* v_inst_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format), 3, 2);
lean_closure_set(v___x_426_, 0, lean_box(0));
lean_closure_set(v___x_426_, 1, v_inst_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToFormat(lean_object* v_00_u03b1_427_, lean_object* v_inst_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_format), 3, 2);
lean_closure_set(v___x_429_, 0, lean_box(0));
lean_closure_set(v___x_429_, 1, v_inst_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = lean_st_ref_get(v_a_430_);
if (lean_obj_tag(v___x_432_) == 1)
{
lean_object* v_head_433_; lean_object* v_tail_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_head_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_head_433_);
v_tail_434_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_tail_434_);
lean_dec_ref_known(v___x_432_, 2);
v___x_435_ = lean_st_ref_swap(v_a_430_, v_tail_434_);
lean_dec(v___x_435_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v_head_433_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec(v___x_432_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg___boxed(lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_440_);
lean_dec(v_a_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f(lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_443_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___boxed(lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f(v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
return v_res_452_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_box(1);
v___x_454_ = l_Lean_MessageData_ofFormat(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(lean_object* v_as_455_, size_t v_sz_456_, size_t v_i_457_, lean_object* v_b_458_){
_start:
{
uint8_t v___x_460_; 
v___x_460_ = lean_usize_dec_lt(v_i_457_, v_sz_456_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_b_458_);
return v___x_461_;
}
else
{
lean_object* v_a_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; size_t v___x_466_; size_t v___x_467_; 
v_a_462_ = lean_array_uget_borrowed(v_as_455_, v_i_457_);
v___x_463_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___closed__0);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v_b_458_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_inc(v_a_462_);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_a_462_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_add(v_i_457_, v___x_466_);
v_i_457_ = v___x_467_;
v_b_458_ = v___x_465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg___boxed(lean_object* v_as_469_, lean_object* v_sz_470_, lean_object* v_i_471_, lean_object* v_b_472_, lean_object* v___y_473_){
_start:
{
size_t v_sz_boxed_474_; size_t v_i_boxed_475_; lean_object* v_res_476_; 
v_sz_boxed_474_ = lean_unbox_usize(v_sz_470_);
lean_dec(v_sz_470_);
v_i_boxed_475_ = lean_unbox_usize(v_i_471_);
lean_dec(v_i_471_);
v_res_476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_as_469_, v_sz_boxed_474_, v_i_boxed_475_, v_b_472_);
lean_dec_ref(v_as_469_);
return v_res_476_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1(void){
_start:
{
lean_object* v___x_478_; lean_object* v_r_479_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__0));
v_r_479_ = l_Lean_stringToMessageData(v___x_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(lean_object* v_f_480_, lean_object* v_args_481_, uint8_t v_parenIfNonAtomic_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_array_get_size(v_args_481_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v_r_489_; size_t v_sz_490_; size_t v___x_491_; lean_object* v___x_492_; 
v_r_489_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___closed__1);
v_sz_490_ = lean_array_size(v_args_481_);
v___x_491_ = ((size_t)0ULL);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_args_481_, v_sz_490_, v___x_491_, v_r_489_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_508_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_508_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_508_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_508_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_unsigned_to_nat(2u);
v___x_498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_a_493_);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v_f_480_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
if (v_parenIfNonAtomic_482_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_500_);
v___x_502_ = v___x_495_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = l_Lean_MessageData_paren(v___x_499_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_504_);
v___x_506_ = v___x_495_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_dec_ref(v_f_480_);
return v___x_492_;
}
}
else
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_f_480_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp___boxed(lean_object* v_f_510_, lean_object* v_args_511_, lean_object* v_parenIfNonAtomic_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
uint8_t v_parenIfNonAtomic_boxed_516_; lean_object* v_res_517_; 
v_parenIfNonAtomic_boxed_516_ = lean_unbox(v_parenIfNonAtomic_512_);
v_res_517_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v_f_510_, v_args_511_, v_parenIfNonAtomic_boxed_516_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec_ref(v_args_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0(lean_object* v_as_518_, size_t v_sz_519_, size_t v_i_520_, lean_object* v_b_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___redArg(v_as_518_, v_sz_519_, v_i_520_, v_b_521_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0___boxed(lean_object* v_as_526_, lean_object* v_sz_527_, lean_object* v_i_528_, lean_object* v_b_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
size_t v_sz_boxed_533_; size_t v_i_boxed_534_; lean_object* v_res_535_; 
v_sz_boxed_533_ = lean_unbox_usize(v_sz_527_);
lean_dec(v_sz_527_);
v_i_boxed_534_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp_spec__0(v_as_526_, v_sz_boxed_533_, v_i_boxed_534_, v_b_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_as_526_);
return v_res_535_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_536_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__0);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
lean_ctor_set(v___x_541_, 2, v___x_540_);
lean_ctor_set(v___x_541_, 3, v___x_540_);
lean_ctor_set(v___x_541_, 4, v___x_539_);
lean_ctor_set(v___x_541_, 5, v___x_539_);
lean_ctor_set(v___x_541_, 6, v___x_539_);
lean_ctor_set(v___x_541_, 7, v___x_539_);
lean_ctor_set(v___x_541_, 8, v___x_539_);
lean_ctor_set(v___x_541_, 9, v___x_539_);
lean_ctor_set(v___x_541_, 10, v___x_539_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(32u);
v___x_543_ = lean_mk_empty_array_with_capacity(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4(void){
_start:
{
size_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_545_ = ((size_t)5ULL);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_unsigned_to_nat(32u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
v___x_549_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__3);
v___x_550_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
lean_ctor_set(v___x_550_, 2, v___x_546_);
lean_ctor_set(v___x_550_, 3, v___x_546_);
lean_ctor_set_usize(v___x_550_, 4, v___x_545_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = lean_box(1);
v___x_552_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__4);
v___x_553_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__1);
v___x_554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v___x_552_);
lean_ctor_set(v___x_554_, 2, v___x_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; lean_object* v_toCold_560_; lean_object* v_env_561_; lean_object* v_options_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_559_ = lean_st_ref_get(v___y_557_);
v_toCold_560_ = lean_ctor_get(v___y_556_, 0);
v_env_561_ = lean_ctor_get(v___x_559_, 0);
lean_inc_ref(v_env_561_);
lean_dec(v___x_559_);
v_options_562_ = lean_ctor_get(v_toCold_560_, 2);
v___x_563_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2);
v___x_564_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5);
lean_inc_ref(v_options_562_);
v___x_565_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_565_, 0, v_env_561_);
lean_ctor_set(v___x_565_, 1, v___x_563_);
lean_ctor_set(v___x_565_, 2, v___x_564_);
lean_ctor_set(v___x_565_, 3, v_options_562_);
v___x_566_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v_msgData_555_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_ref_577_; lean_object* v___x_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_587_; 
v_ref_577_ = lean_ctor_get(v___y_574_, 2);
v___x_578_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_573_, v___y_574_, v___y_575_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_587_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
lean_inc(v_ref_577_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_ref_577_);
lean_ctor_set(v___x_583_, 1, v_a_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 1);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_585_ = v___x_581_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_593_, lean_object* v_msg_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_toCold_599_; lean_object* v_currRecDepth_600_; lean_object* v_ref_601_; uint8_t v_diag_602_; uint8_t v_suppressElabErrors_603_; lean_object* v_ref_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_toCold_599_ = lean_ctor_get(v___y_596_, 0);
v_currRecDepth_600_ = lean_ctor_get(v___y_596_, 1);
v_ref_601_ = lean_ctor_get(v___y_596_, 2);
v_diag_602_ = lean_ctor_get_uint8(v___y_596_, sizeof(void*)*3);
v_suppressElabErrors_603_ = lean_ctor_get_uint8(v___y_596_, sizeof(void*)*3 + 1);
v_ref_604_ = l_Lean_replaceRef(v_ref_593_, v_ref_601_);
lean_inc(v_currRecDepth_600_);
lean_inc_ref(v_toCold_599_);
v___x_605_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_605_, 0, v_toCold_599_);
lean_ctor_set(v___x_605_, 1, v_currRecDepth_600_);
lean_ctor_set(v___x_605_, 2, v_ref_604_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*3, v_diag_602_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*3 + 1, v_suppressElabErrors_603_);
v___x_606_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_594_, v___x_605_, v___y_597_);
lean_dec_ref_known(v___x_605_, 3);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_607_, lean_object* v_msg_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_607_, v_msg_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec(v_ref_607_);
return v_res_613_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0));
v___x_616_ = l_Lean_stringToMessageData(v___x_615_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2));
v___x_619_ = l_Lean_stringToMessageData(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_628_ = l_Lean_stringToMessageData(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_631_ = l_Lean_stringToMessageData(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_634_ = l_Lean_stringToMessageData(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_635_, lean_object* v_declHint_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v_env_640_; uint8_t v___x_641_; 
v___x_639_ = lean_st_ref_get(v___y_637_);
v_env_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc_ref(v_env_640_);
lean_dec(v___x_639_);
v___x_641_ = l_Lean_Name_isAnonymous(v_declHint_636_);
if (v___x_641_ == 0)
{
uint8_t v_isExporting_642_; 
v_isExporting_642_ = lean_ctor_get_uint8(v_env_640_, sizeof(void*)*8);
if (v_isExporting_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_env_640_);
lean_dec(v_declHint_636_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_msg_635_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; uint8_t v___x_645_; 
lean_inc_ref(v_env_640_);
v___x_644_ = l_Lean_Environment_setExporting(v_env_640_, v___x_641_);
lean_inc(v_declHint_636_);
lean_inc_ref(v___x_644_);
v___x_645_ = l_Lean_Environment_contains(v___x_644_, v_declHint_636_, v_isExporting_642_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec_ref(v___x_644_);
lean_dec_ref(v_env_640_);
lean_dec(v_declHint_636_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v_msg_635_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v_c_652_; lean_object* v___x_653_; 
v___x_647_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2);
v___x_648_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5);
v___x_649_ = l_Lean_Options_empty;
v___x_650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_650_, 0, v___x_644_);
lean_ctor_set(v___x_650_, 1, v___x_647_);
lean_ctor_set(v___x_650_, 2, v___x_648_);
lean_ctor_set(v___x_650_, 3, v___x_649_);
lean_inc(v_declHint_636_);
v___x_651_ = l_Lean_MessageData_ofConstName(v_declHint_636_, v___x_641_);
v_c_652_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_652_, 0, v___x_650_);
lean_ctor_set(v_c_652_, 1, v___x_651_);
v___x_653_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_640_, v_declHint_636_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec_ref(v_env_640_);
lean_dec(v_declHint_636_);
v___x_654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_c_652_);
v___x_656_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = l_Lean_MessageData_note(v___x_657_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v_msg_635_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
else
{
lean_object* v_val_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_696_; 
v_val_661_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_696_ == 0)
{
v___x_663_ = v___x_653_;
v_isShared_664_ = v_isSharedCheck_696_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_val_661_);
lean_dec(v___x_653_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_696_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_mod_668_; uint8_t v___x_669_; 
v___x_665_ = lean_box(0);
v___x_666_ = l_Lean_Environment_header(v_env_640_);
lean_dec_ref(v_env_640_);
v___x_667_ = l_Lean_EnvironmentHeader_moduleNames(v___x_666_);
v_mod_668_ = lean_array_get(v___x_665_, v___x_667_, v_val_661_);
lean_dec(v_val_661_);
lean_dec_ref(v___x_667_);
v___x_669_ = l_Lean_isPrivateName(v_declHint_636_);
lean_dec(v_declHint_636_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_c_652_);
v___x_672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_MessageData_ofName(v_mod_668_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_Lean_MessageData_note(v___x_677_);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v_msg_635_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 0);
lean_ctor_set(v___x_663_, 0, v___x_679_);
v___x_681_ = v___x_663_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v_c_652_);
v___x_685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Lean_MessageData_ofName(v_mod_668_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Lean_MessageData_note(v___x_690_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v_msg_635_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 0);
lean_ctor_set(v___x_663_, 0, v___x_692_);
v___x_694_ = v___x_663_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_697_; 
lean_dec_ref(v_env_640_);
lean_dec(v_declHint_636_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v_msg_635_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_698_, lean_object* v_declHint_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_698_, v_declHint_699_, v___y_700_);
lean_dec(v___y_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_703_, lean_object* v_declHint_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
v___x_709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_703_, v_declHint_704_, v___y_707_);
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = l_Lean_unknownIdentifierMessageTag;
v___x_715_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v_a_710_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_715_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_720_, lean_object* v_declHint_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_720_, v_declHint_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_727_, lean_object* v_msg_728_, lean_object* v_declHint_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; lean_object* v_a_735_; lean_object* v___x_736_; 
v___x_734_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_728_, v_declHint_729_, v___y_730_, v___y_731_, v___y_732_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_727_, v_a_735_, v___y_730_, v___y_731_, v___y_732_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_737_, lean_object* v_msg_738_, lean_object* v_declHint_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_737_, v_msg_738_, v_declHint_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v_ref_737_);
return v_res_744_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_751_, lean_object* v_constName_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_757_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
v___x_758_ = 0;
lean_inc(v_constName_752_);
v___x_759_ = l_Lean_MessageData_ofConstName(v_constName_752_, v___x_758_);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_751_, v___x_762_, v_constName_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_764_, lean_object* v_constName_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_764_, v_constName_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec(v_ref_764_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_ref_776_; lean_object* v___x_777_; 
v_ref_776_ = lean_ctor_get(v___y_773_, 2);
v___x_777_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_776_, v_constName_771_, v___y_772_, v___y_773_, v___y_774_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(lean_object* v_constName_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v_env_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_st_ref_get(v___y_787_);
v_env_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_env_790_);
lean_dec(v___x_789_);
v___x_791_ = 0;
lean_inc(v_constName_784_);
v___x_792_ = l_Lean_Environment_findConstVal_x3f(v_env_790_, v_constName_784_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_793_;
}
else
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_constName_784_);
v_val_794_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_792_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v___x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 0);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_val_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0___boxed(lean_object* v_constName_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v___x_810_; 
v___x_810_ = l_List_reverse___redArg(v_a_809_);
return v___x_810_;
}
else
{
lean_object* v_head_811_; lean_object* v_tail_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_821_; 
v_head_811_ = lean_ctor_get(v_a_808_, 0);
v_tail_812_ = lean_ctor_get(v_a_808_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_821_ == 0)
{
v___x_814_ = v_a_808_;
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_tail_812_);
lean_inc(v_head_811_);
lean_dec(v_a_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = l_Lean_mkLevelParam(v_head_811_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_a_809_);
lean_ctor_set(v___x_814_, 0, v___x_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_a_809_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_a_808_ = v_tail_812_;
v_a_809_ = v___x_818_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(lean_object* v_constName_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
lean_inc(v_constName_822_);
v___x_827_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_839_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_839_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_levelParams_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v_levelParams_832_ = lean_ctor_get(v_a_828_, 1);
lean_inc(v_levelParams_832_);
lean_dec(v_a_828_);
v___x_833_ = lean_box(0);
v___x_834_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(v_levelParams_832_, v___x_833_);
v___x_835_ = l_Lean_mkConst(v_constName_822_, v___x_834_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_835_);
v___x_837_ = v___x_830_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_constName_822_);
v_a_840_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_827_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_827_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0___boxed(lean_object* v_constName_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_constName_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
return v_res_853_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1));
v___x_860_ = l_Lean_MessageData_ofFormat(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4));
v___x_865_ = l_Lean_MessageData_ofFormat(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__6));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(uint8_t v_parenIfNonAtomic_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_872_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_995_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_995_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_995_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_995_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 1)
{
lean_object* v_val_881_; 
v_val_881_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_a_877_, 1);
switch(lean_obj_tag(v_val_881_))
{
case 0:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
case 1:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_886_);
v___x_888_ = v___x_879_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
case 2:
{
lean_object* v_a_890_; 
v_a_890_ = lean_ctor_get(v_val_881_, 0);
lean_inc_ref(v_a_890_);
lean_dec_ref_known(v_val_881_, 1);
if (lean_obj_tag(v_a_890_) == 0)
{
lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_903_; 
v_val_891_ = lean_ctor_get(v_a_890_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v_a_890_);
if (v_isSharedCheck_903_ == 0)
{
v___x_893_ = v_a_890_;
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_dec(v_a_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = l_Nat_reprFast(v_val_891_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 3);
lean_ctor_set(v___x_893_, 0, v___x_895_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_902_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = l_Lean_MessageData_ofFormat(v___x_897_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_898_);
v___x_900_ = v___x_879_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v_val_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v_val_904_ = lean_ctor_get(v_a_890_, 0);
lean_inc_ref(v_val_904_);
lean_dec_ref_known(v_a_890_, 1);
v___x_905_ = l_Lean_stringToMessageData(v_val_904_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_905_);
v___x_907_ = v___x_879_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
case 3:
{
lean_object* v_a_909_; lean_object* v_a_910_; lean_object* v___x_911_; 
lean_del_object(v___x_879_);
v_a_909_ = lean_ctor_get(v_val_881_, 0);
lean_inc(v_a_909_);
v_a_910_ = lean_ctor_get(v_val_881_, 1);
lean_inc(v_a_910_);
lean_dec_ref_known(v_val_881_, 2);
v___x_911_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_910_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = l_Lean_mkFVar(v_a_909_);
v___x_914_ = l_Lean_MessageData_ofExpr(v___x_913_);
v___x_915_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_914_, v_a_912_, v_parenIfNonAtomic_871_, v_a_873_, v_a_874_);
lean_dec(v_a_912_);
return v___x_915_;
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_909_);
v_a_916_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_911_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_911_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
case 4:
{
lean_object* v_a_924_; lean_object* v_a_925_; lean_object* v___x_926_; 
lean_del_object(v___x_879_);
v_a_924_ = lean_ctor_get(v_val_881_, 0);
lean_inc(v_a_924_);
v_a_925_ = lean_ctor_get(v_val_881_, 1);
lean_inc(v_a_925_);
lean_dec_ref_known(v_val_881_, 2);
v___x_926_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_a_924_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_928_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
v___x_928_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_925_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_925_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = l_Lean_MessageData_ofExpr(v_a_927_);
v___x_931_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_930_, v_a_929_, v_parenIfNonAtomic_871_, v_a_873_, v_a_874_);
lean_dec(v_a_929_);
return v___x_931_;
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_a_927_);
v_a_932_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_928_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_a_925_);
v_a_940_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_926_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_926_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
case 5:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_del_object(v___x_879_);
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v___x_948_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7);
v___x_952_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_951_, v_a_950_, v_parenIfNonAtomic_871_, v_a_873_, v_a_874_);
lean_dec(v_a_950_);
return v___x_952_;
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_953_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_949_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_949_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
default: 
{
lean_object* v_a_961_; lean_object* v_a_962_; uint8_t v___x_963_; lean_object* v___x_964_; 
lean_del_object(v___x_879_);
v_a_961_ = lean_ctor_get(v_val_881_, 1);
lean_inc(v_a_961_);
v_a_962_ = lean_ctor_get(v_val_881_, 2);
lean_inc(v_a_962_);
lean_dec_ref_known(v_val_881_, 3);
v___x_963_ = 1;
v___x_964_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_963_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_990_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_990_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_990_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_990_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; 
v___x_969_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_962_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_962_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v_a_965_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_add(v_a_961_, v___x_973_);
lean_dec(v_a_961_);
v___x_975_ = l_Nat_reprFast(v___x_974_);
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 3);
lean_ctor_set(v___x_967_, 0, v___x_975_);
v___x_977_ = v___x_967_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_MessageData_ofFormat(v___x_977_);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_972_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_979_, v_a_970_, v_parenIfNonAtomic_871_, v_a_873_, v_a_874_);
lean_dec(v_a_970_);
return v___x_980_;
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_del_object(v___x_967_);
lean_dec(v_a_965_);
lean_dec(v_a_961_);
v_a_982_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_969_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_969_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
else
{
lean_dec(v_a_962_);
lean_dec(v_a_961_);
return v___x_964_;
}
}
}
}
else
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec(v_a_877_);
v___x_991_ = l_Lean_MessageData_nil;
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_991_);
v___x_993_ = v___x_879_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
v_a_996_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_876_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_876_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(lean_object* v_upperBound_1004_, lean_object* v_a_1005_, lean_object* v_b_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
uint8_t v___x_1011_; 
v___x_1011_ = lean_nat_dec_lt(v_a_1005_, v_upperBound_1004_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
lean_dec(v_a_1005_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_b_1006_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1011_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = lean_array_push(v_b_1006_, v_a_1014_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_a_1005_, v___x_1016_);
lean_dec(v_a_1005_);
v_a_1005_ = v___x_1017_;
v_b_1006_ = v___x_1015_;
goto _start;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v_b_1006_);
lean_dec(v_a_1005_);
v_a_1019_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1013_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1013_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(lean_object* v_num_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v_r_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_unsigned_to_nat(0u);
v_r_1033_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0));
v___x_1034_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_num_1027_, v___x_1032_, v_r_1033_, v_a_1028_, v_a_1029_, v_a_1030_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___boxed(lean_object* v_num_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_num_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec(v_num_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg___boxed(lean_object* v_upperBound_1041_, lean_object* v_a_1042_, lean_object* v_b_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_1041_, v_a_1042_, v_b_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec(v_upperBound_1041_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___boxed(lean_object* v_parenIfNonAtomic_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
uint8_t v_parenIfNonAtomic_boxed_1054_; lean_object* v_res_1055_; 
v_parenIfNonAtomic_boxed_1054_ = lean_unbox(v_parenIfNonAtomic_1049_);
v_res_1055_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v_parenIfNonAtomic_boxed_1054_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(lean_object* v_upperBound_1056_, lean_object* v_inst_1057_, lean_object* v_R_1058_, lean_object* v_a_1059_, lean_object* v_b_1060_, lean_object* v_c_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_1056_, v_a_1059_, v_b_1060_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___boxed(lean_object* v_upperBound_1067_, lean_object* v_inst_1068_, lean_object* v_R_1069_, lean_object* v_a_1070_, lean_object* v_b_1071_, lean_object* v_c_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(v_upperBound_1067_, v_inst_1068_, v_R_1069_, v_a_1070_, v_b_1071_, v_c_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v_upperBound_1067_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1078_, lean_object* v_constName_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1085_, lean_object* v_constName_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(v_00_u03b1_1085_, v_constName_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_1092_, lean_object* v_ref_1093_, lean_object* v_constName_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1093_, v_constName_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1100_, lean_object* v_ref_1101_, lean_object* v_constName_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_1100_, v_ref_1101_, v_constName_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v_ref_1101_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1108_, lean_object* v_ref_1109_, lean_object* v_msg_1110_, lean_object* v_declHint_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1109_, v_msg_1110_, v_declHint_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_ref_1118_, lean_object* v_msg_1119_, lean_object* v_declHint_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_1117_, v_ref_1118_, v_msg_1119_, v_declHint_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec(v_ref_1118_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_1126_, lean_object* v_declHint_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1126_, v_declHint_1127_, v___y_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_1133_, lean_object* v_declHint_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_1133_, v_declHint_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1140_, lean_object* v_ref_1141_, lean_object* v_msg_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_1141_, v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_ref_1149_, lean_object* v_msg_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1148_, v_ref_1149_, v_msg_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec(v_ref_1149_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_1156_, lean_object* v_msg_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1157_, v___y_1159_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_msg_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_1163_, v_msg_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern(lean_object* v_keys_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = lean_array_to_list(v_keys_1170_);
v___x_1175_ = lean_st_mk_ref(v___x_1174_);
v___x_1176_ = 0;
v___x_1177_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1176_, v___x_1175_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1186_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1186_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = lean_st_ref_get(v___x_1175_);
lean_dec(v___x_1175_);
lean_dec(v___x_1182_);
if (v_isShared_1181_ == 0)
{
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1178_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
lean_dec(v___x_1175_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern___boxed(lean_object* v_keys_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1187_, v_a_1188_, v_a_1189_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object* v_keys_1194_, lean_object* v_v_1195_, lean_object* v_i_1196_){
_start:
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_array_get_size(v_keys_1194_);
v___x_1198_ = lean_nat_dec_lt(v_i_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_mk_empty_array_with_capacity(v___x_1199_);
v___x_1201_ = lean_array_push(v___x_1200_, v_v_1195_);
v___x_1202_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0));
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
return v___x_1203_;
}
else
{
lean_object* v_k_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_c_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_k_1204_ = lean_array_fget_borrowed(v_keys_1194_, v_i_1196_);
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_add(v_i_1196_, v___x_1205_);
v_c_1207_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1194_, v_v_1195_, v___x_1206_);
lean_dec(v___x_1206_);
v___x_1208_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0));
lean_inc(v_k_1204_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_k_1204_);
lean_ctor_set(v___x_1209_, 1, v_c_1207_);
v___x_1210_ = lean_mk_empty_array_with_capacity(v___x_1205_);
v___x_1211_ = lean_array_push(v___x_1210_, v___x_1209_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1208_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___boxed(lean_object* v_keys_1213_, lean_object* v_v_1214_, lean_object* v_i_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1213_, v_v_1214_, v_i_1215_);
lean_dec(v_i_1215_);
lean_dec_ref(v_keys_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object* v_00_u03b1_1217_, lean_object* v_keys_1218_, lean_object* v_v_1219_, lean_object* v_i_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1218_, v_v_1219_, v_i_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___boxed(lean_object* v_00_u03b1_1222_, lean_object* v_keys_1223_, lean_object* v_v_1224_, lean_object* v_i_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(v_00_u03b1_1222_, v_keys_1223_, v_v_1224_, v_i_1225_);
lean_dec(v_i_1225_);
lean_dec_ref(v_keys_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(lean_object* v_inst_1227_, lean_object* v_vs_1228_, lean_object* v_v_1229_, lean_object* v_i_1230_){
_start:
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = lean_array_get_size(v_vs_1228_);
v___x_1232_ = lean_nat_dec_lt(v_i_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec(v_i_1230_);
lean_dec_ref(v_inst_1227_);
v___x_1233_ = lean_array_push(v_vs_1228_, v_v_1229_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1234_ = lean_array_fget_borrowed(v_vs_1228_, v_i_1230_);
lean_inc_ref(v_inst_1227_);
lean_inc(v___x_1234_);
lean_inc(v_v_1229_);
v___x_1235_ = lean_apply_2(v_inst_1227_, v_v_1229_, v___x_1234_);
v___x_1236_ = lean_unbox(v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_add(v_i_1230_, v___x_1237_);
lean_dec(v_i_1230_);
v_i_1230_ = v___x_1238_;
goto _start;
}
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v_inst_1227_);
v___x_1240_ = lean_array_fset(v_vs_1228_, v_i_1230_, v_v_1229_);
lean_dec(v_i_1230_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop(lean_object* v_00_u03b1_1241_, lean_object* v_inst_1242_, lean_object* v_vs_1243_, lean_object* v_v_1244_, lean_object* v_i_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(v_inst_1242_, v_vs_1243_, v_v_1244_, v_i_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(lean_object* v_inst_1247_, lean_object* v_vs_1248_, lean_object* v_v_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(v_inst_1247_, v_vs_1248_, v_v_1249_, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal(lean_object* v_00_u03b1_1252_, lean_object* v_inst_1253_, lean_object* v_vs_1254_, lean_object* v_v_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_1253_, v_vs_1254_, v_v_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(lean_object* v_a_1257_, lean_object* v_b_1258_){
_start:
{
lean_object* v_fst_1259_; lean_object* v_fst_1260_; uint8_t v___x_1261_; 
v_fst_1259_ = lean_ctor_get(v_a_1257_, 0);
v_fst_1260_ = lean_ctor_get(v_b_1258_, 0);
v___x_1261_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1259_, v_fst_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed(lean_object* v_a_1262_, lean_object* v_b_1263_){
_start:
{
uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_res_1264_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(v_a_1262_, v_b_1263_);
lean_dec_ref(v_b_1263_);
lean_dec_ref(v_a_1262_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(lean_object* v_x_1266_, lean_object* v_keys_1267_, lean_object* v_v_1268_, lean_object* v_k_1269_, lean_object* v_x_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_c_1273_; lean_object* v___x_1274_; 
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_x_1266_, v___x_1271_);
v_c_1273_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1267_, v_v_1268_, v___x_1272_);
lean_dec(v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_k_1269_);
lean_ctor_set(v___x_1274_, 1, v_c_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed(lean_object* v_x_1275_, lean_object* v_keys_1276_, lean_object* v_v_1277_, lean_object* v_k_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(v_x_1275_, v_keys_1276_, v_v_1277_, v_k_1278_, v_x_1279_);
lean_dec_ref(v_keys_1276_);
lean_dec(v_x_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed(lean_object* v_x_1301_, lean_object* v_inst_1302_, lean_object* v_keys_1303_, lean_object* v_v_1304_, lean_object* v_k_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(v_x_1301_, v_inst_1302_, v_keys_1303_, v_v_1304_, v_k_1305_, v_x_1306_);
lean_dec(v_x_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(lean_object* v_inst_1308_, lean_object* v_keys_1309_, lean_object* v_v_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v_vs_1314_; lean_object* v_children_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1335_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__9));
v_vs_1314_ = lean_ctor_get(v_x_1312_, 0);
v_children_1315_ = lean_ctor_get(v_x_1312_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1312_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1317_ = v_x_1312_;
v_isShared_1318_ = v_isSharedCheck_1335_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_children_1315_);
lean_inc(v_vs_1314_);
lean_dec(v_x_1312_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1335_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = lean_array_get_size(v_keys_1309_);
v___x_1320_ = lean_nat_dec_lt(v_x_1311_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_dec(v_x_1311_);
lean_dec_ref(v_keys_1309_);
v___x_1321_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_1308_, v_vs_1314_, v_v_1310_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1321_);
v___x_1323_ = v___x_1317_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_children_1315_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
else
{
lean_object* v___f_1325_; lean_object* v_k_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_c_1331_; lean_object* v___x_1333_; 
v___f_1325_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v_k_1326_ = lean_array_fget(v_keys_1309_, v_x_1311_);
lean_inc_n(v_k_1326_, 2);
lean_inc(v_v_1310_);
lean_inc_ref(v_keys_1309_);
lean_inc(v_x_1311_);
v___f_1327_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1327_, 0, v_x_1311_);
lean_closure_set(v___f_1327_, 1, v_inst_1308_);
lean_closure_set(v___f_1327_, 2, v_keys_1309_);
lean_closure_set(v___f_1327_, 3, v_v_1310_);
lean_closure_set(v___f_1327_, 4, v_k_1326_);
v___f_1328_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1328_, 0, v_x_1311_);
lean_closure_set(v___f_1328_, 1, v_keys_1309_);
lean_closure_set(v___f_1328_, 2, v_v_1310_);
lean_closure_set(v___f_1328_, 3, v_k_1326_);
v___x_1329_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1));
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_k_1326_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v_c_1331_ = l_Array_binInsertM___redArg(v___x_1313_, v___f_1325_, v___f_1327_, v___f_1328_, v_children_1315_, v___x_1330_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_c_1331_);
v___x_1333_ = v___x_1317_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_vs_1314_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_c_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(lean_object* v_x_1336_, lean_object* v_inst_1337_, lean_object* v_keys_1338_, lean_object* v_v_1339_, lean_object* v_k_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v_snd_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
v_snd_1342_ = lean_ctor_get(v_x_1341_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1341_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_x_1341_, 0);
lean_dec(v_unused_1353_);
v___x_1344_ = v_x_1341_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1342_);
lean_dec(v_x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_c_1348_; lean_object* v___x_1350_; 
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_add(v_x_1336_, v___x_1346_);
v_c_1348_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1337_, v_keys_1338_, v_v_1339_, v___x_1347_, v_snd_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v_c_1348_);
lean_ctor_set(v___x_1344_, 0, v_k_1340_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_k_1340_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_c_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux(lean_object* v_00_u03b1_1354_, lean_object* v_inst_1355_, lean_object* v_keys_1356_, lean_object* v_v_1357_, lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1355_, v_keys_1356_, v_v_1357_, v_x_1358_, v_x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg___lam__0(lean_object* v_keys_1361_, lean_object* v_v_1362_, lean_object* v_inst_1363_, lean_object* v_x_1364_){
_start:
{
if (lean_obj_tag(v_x_1364_) == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec_ref(v_inst_1363_);
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1361_, v_v_1362_, v___x_1365_);
lean_dec_ref(v_keys_1361_);
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1377_; 
v_val_1368_ = lean_ctor_get(v_x_1364_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1370_ = v_x_1364_;
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_val_1368_);
lean_dec(v_x_1364_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1363_, v_keys_1361_, v_v_1362_, v___x_1372_, v_val_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1373_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2(void){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1384_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5));
v___x_1385_ = lean_unsigned_to_nat(23u);
v___x_1386_ = lean_unsigned_to_nat(166u);
v___x_1387_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4));
v___x_1388_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3));
v___x_1389_ = l_mkPanicMessageWithDecl(v___x_1388_, v___x_1387_, v___x_1386_, v___x_1385_, v___x_1384_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg(lean_object* v_inst_1390_, lean_object* v_d_1391_, lean_object* v_keys_1392_, lean_object* v_v_1393_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_array_get_size(v_keys_1392_);
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_nat_dec_eq(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___f_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_k_1401_; uint64_t v___x_1402_; size_t v_h_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v_keys_1392_);
v___f_1397_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1397_, 0, v_keys_1392_);
lean_closure_set(v___f_1397_, 1, v_v_1393_);
lean_closure_set(v___f_1397_, 2, v_inst_1390_);
v___x_1398_ = lean_box(0);
v___x_1399_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0));
v___x_1400_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1));
v_k_1401_ = lean_array_get(v___x_1398_, v_keys_1392_, v___x_1395_);
lean_dec_ref(v_keys_1392_);
v___x_1402_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1401_);
v_h_1403_ = lean_uint64_to_usize(v___x_1402_);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = l_Lean_PersistentHashMap_alterAux___redArg(v___x_1399_, v___x_1400_, v___f_1397_, v_d_1391_, v_h_1403_, v___x_1404_, v_k_1401_);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec(v_v_1393_);
lean_dec_ref(v_keys_1392_);
lean_dec_ref(v_d_1391_);
lean_dec_ref(v_inst_1390_);
v___x_1406_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2, &l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2);
v___x_1407_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6, &l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6);
v___x_1408_ = l_panic___redArg(v___x_1406_, v___x_1407_);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue(lean_object* v_00_u03b1_1409_, lean_object* v_inst_1410_, lean_object* v_d_1411_, lean_object* v_keys_1412_, lean_object* v_v_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_1410_, v_d_1411_, v_keys_1412_, v_v_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___redArg(lean_object* v_inst_1415_, lean_object* v_d_1416_, lean_object* v_keys_1417_, lean_object* v_v_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_1415_, v_d_1416_, v_keys_1417_, v_v_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object* v_00_u03b1_1420_, lean_object* v_inst_1421_, lean_object* v_d_1422_, lean_object* v_keys_1423_, lean_object* v_v_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_1421_, v_d_1422_, v_keys_1423_, v_v_1424_);
return v___x_1425_;
}
}
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
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
