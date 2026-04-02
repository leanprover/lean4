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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_ctorIdx(lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_binInsertM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_9_);
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
lean_dec_ref(v_k_128_);
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
lean_dec_ref(v_k_128_);
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
lean_dec_ref(v_k_128_);
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
lean_dec_ref(v_k_128_);
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
lean_dec_ref(v_x_240_);
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
lean_dec_ref(v_x_240_);
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
lean_dec_ref(v___x_432_);
v___x_435_ = lean_st_ref_set(v_a_430_, v_tail_434_);
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
v___x_541_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_559_; lean_object* v_env_560_; lean_object* v_options_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_559_ = lean_st_ref_get(v___y_557_);
v_env_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc_ref(v_env_560_);
lean_dec(v___x_559_);
v_options_561_ = lean_ctor_get(v___y_556_, 2);
v___x_562_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2);
v___x_563_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5);
lean_inc_ref(v_options_561_);
v___x_564_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_564_, 0, v_env_560_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
lean_ctor_set(v___x_564_, 2, v___x_563_);
lean_ctor_set(v___x_564_, 3, v_options_561_);
v___x_565_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v_msgData_555_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_ref_576_; lean_object* v___x_577_; lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
v_ref_576_ = lean_ctor_get(v___y_573_, 5);
v___x_577_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_572_, v___y_573_, v___y_574_);
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
lean_inc(v_ref_576_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_ref_576_);
lean_ctor_set(v___x_582_, 1, v_a_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 1);
lean_ctor_set(v___x_580_, 0, v___x_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_592_, lean_object* v_msg_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_fileName_598_; lean_object* v_fileMap_599_; lean_object* v_options_600_; lean_object* v_currRecDepth_601_; lean_object* v_maxRecDepth_602_; lean_object* v_ref_603_; lean_object* v_currNamespace_604_; lean_object* v_openDecls_605_; lean_object* v_initHeartbeats_606_; lean_object* v_maxHeartbeats_607_; lean_object* v_quotContext_608_; lean_object* v_currMacroScope_609_; uint8_t v_diag_610_; lean_object* v_cancelTk_x3f_611_; uint8_t v_suppressElabErrors_612_; lean_object* v_inheritedTraceOptions_613_; lean_object* v_ref_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_fileName_598_ = lean_ctor_get(v___y_595_, 0);
v_fileMap_599_ = lean_ctor_get(v___y_595_, 1);
v_options_600_ = lean_ctor_get(v___y_595_, 2);
v_currRecDepth_601_ = lean_ctor_get(v___y_595_, 3);
v_maxRecDepth_602_ = lean_ctor_get(v___y_595_, 4);
v_ref_603_ = lean_ctor_get(v___y_595_, 5);
v_currNamespace_604_ = lean_ctor_get(v___y_595_, 6);
v_openDecls_605_ = lean_ctor_get(v___y_595_, 7);
v_initHeartbeats_606_ = lean_ctor_get(v___y_595_, 8);
v_maxHeartbeats_607_ = lean_ctor_get(v___y_595_, 9);
v_quotContext_608_ = lean_ctor_get(v___y_595_, 10);
v_currMacroScope_609_ = lean_ctor_get(v___y_595_, 11);
v_diag_610_ = lean_ctor_get_uint8(v___y_595_, sizeof(void*)*14);
v_cancelTk_x3f_611_ = lean_ctor_get(v___y_595_, 12);
v_suppressElabErrors_612_ = lean_ctor_get_uint8(v___y_595_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_613_ = lean_ctor_get(v___y_595_, 13);
v_ref_614_ = l_Lean_replaceRef(v_ref_592_, v_ref_603_);
lean_inc_ref(v_inheritedTraceOptions_613_);
lean_inc(v_cancelTk_x3f_611_);
lean_inc(v_currMacroScope_609_);
lean_inc(v_quotContext_608_);
lean_inc(v_maxHeartbeats_607_);
lean_inc(v_initHeartbeats_606_);
lean_inc(v_openDecls_605_);
lean_inc(v_currNamespace_604_);
lean_inc(v_maxRecDepth_602_);
lean_inc(v_currRecDepth_601_);
lean_inc_ref(v_options_600_);
lean_inc_ref(v_fileMap_599_);
lean_inc_ref(v_fileName_598_);
v___x_615_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_615_, 0, v_fileName_598_);
lean_ctor_set(v___x_615_, 1, v_fileMap_599_);
lean_ctor_set(v___x_615_, 2, v_options_600_);
lean_ctor_set(v___x_615_, 3, v_currRecDepth_601_);
lean_ctor_set(v___x_615_, 4, v_maxRecDepth_602_);
lean_ctor_set(v___x_615_, 5, v_ref_614_);
lean_ctor_set(v___x_615_, 6, v_currNamespace_604_);
lean_ctor_set(v___x_615_, 7, v_openDecls_605_);
lean_ctor_set(v___x_615_, 8, v_initHeartbeats_606_);
lean_ctor_set(v___x_615_, 9, v_maxHeartbeats_607_);
lean_ctor_set(v___x_615_, 10, v_quotContext_608_);
lean_ctor_set(v___x_615_, 11, v_currMacroScope_609_);
lean_ctor_set(v___x_615_, 12, v_cancelTk_x3f_611_);
lean_ctor_set(v___x_615_, 13, v_inheritedTraceOptions_613_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*14, v_diag_610_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*14 + 1, v_suppressElabErrors_612_);
v___x_616_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_593_, v___x_615_, v___y_596_);
lean_dec_ref(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_617_, lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_617_, v_msg_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec(v_ref_617_);
return v_res_623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__0));
v___x_626_ = l_Lean_stringToMessageData(v___x_625_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__2));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__4));
v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_638_ = l_Lean_stringToMessageData(v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_645_, lean_object* v_declHint_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; lean_object* v_env_650_; uint8_t v___x_651_; 
v___x_649_ = lean_st_ref_get(v___y_647_);
v_env_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_env_650_);
lean_dec(v___x_649_);
v___x_651_ = l_Lean_Name_isAnonymous(v_declHint_646_);
if (v___x_651_ == 0)
{
uint8_t v_isExporting_652_; 
v_isExporting_652_ = lean_ctor_get_uint8(v_env_650_, sizeof(void*)*8);
if (v_isExporting_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v_env_650_);
lean_dec(v_declHint_646_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_msg_645_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; uint8_t v___x_655_; 
lean_inc_ref(v_env_650_);
v___x_654_ = l_Lean_Environment_setExporting(v_env_650_, v___x_651_);
lean_inc(v_declHint_646_);
lean_inc_ref(v___x_654_);
v___x_655_ = l_Lean_Environment_contains(v___x_654_, v_declHint_646_, v_isExporting_652_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v___x_654_);
lean_dec_ref(v_env_650_);
lean_dec(v_declHint_646_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_msg_645_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_c_662_; lean_object* v___x_663_; 
v___x_657_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__2);
v___x_658_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10_spec__11___closed__5);
v___x_659_ = l_Lean_Options_empty;
v___x_660_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_660_, 0, v___x_654_);
lean_ctor_set(v___x_660_, 1, v___x_657_);
lean_ctor_set(v___x_660_, 2, v___x_658_);
lean_ctor_set(v___x_660_, 3, v___x_659_);
lean_inc(v_declHint_646_);
v___x_661_ = l_Lean_MessageData_ofConstName(v_declHint_646_, v___x_651_);
v_c_662_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_662_, 0, v___x_660_);
lean_ctor_set(v_c_662_, 1, v___x_661_);
v___x_663_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_650_, v_declHint_646_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec_ref(v_env_650_);
lean_dec(v_declHint_646_);
v___x_664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v_c_662_);
v___x_666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_MessageData_note(v___x_667_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v_msg_645_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
else
{
lean_object* v_val_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_706_; 
v_val_671_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_706_ == 0)
{
v___x_673_ = v___x_663_;
v_isShared_674_ = v_isSharedCheck_706_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_val_671_);
lean_dec(v___x_663_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_706_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_mod_678_; uint8_t v___x_679_; 
v___x_675_ = lean_box(0);
v___x_676_ = l_Lean_Environment_header(v_env_650_);
lean_dec_ref(v_env_650_);
v___x_677_ = l_Lean_EnvironmentHeader_moduleNames(v___x_676_);
v_mod_678_ = lean_array_get(v___x_675_, v___x_677_, v_val_671_);
lean_dec(v_val_671_);
lean_dec_ref(v___x_677_);
v___x_679_ = l_Lean_isPrivateName(v_declHint_646_);
lean_dec(v_declHint_646_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v_c_662_);
v___x_682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Lean_MessageData_ofName(v_mod_678_);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l_Lean_MessageData_note(v___x_687_);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v_msg_645_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 0);
lean_ctor_set(v___x_673_, 0, v___x_689_);
v___x_691_ = v___x_673_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_c_662_);
v___x_695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_MessageData_ofName(v_mod_678_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_MessageData_note(v___x_700_);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v_msg_645_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 0);
lean_ctor_set(v___x_673_, 0, v___x_702_);
v___x_704_ = v___x_673_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_707_; 
lean_dec_ref(v_env_650_);
lean_dec(v_declHint_646_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_msg_645_);
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_708_, lean_object* v_declHint_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_708_, v_declHint_709_, v___y_710_);
lean_dec(v___y_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(lean_object* v_msg_713_, lean_object* v_declHint_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_729_; 
v___x_719_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_713_, v_declHint_714_, v___y_717_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_729_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_729_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_724_ = l_Lean_unknownIdentifierMessageTag;
v___x_725_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_a_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_725_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_730_, lean_object* v_declHint_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_730_, v_declHint_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(lean_object* v_ref_737_, lean_object* v_msg_738_, lean_object* v_declHint_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v_a_745_; lean_object* v___x_746_; 
v___x_744_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7(v_msg_738_, v_declHint_739_, v___y_740_, v___y_741_, v___y_742_);
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref(v___x_744_);
v___x_746_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_737_, v_a_745_, v___y_740_, v___y_741_, v___y_742_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_ref_747_, lean_object* v_msg_748_, lean_object* v_declHint_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_747_, v_msg_748_, v_declHint_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec(v_ref_747_);
return v_res_754_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__2));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_ref_761_, lean_object* v_constName_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_767_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
v___x_768_ = 0;
lean_inc(v_constName_762_);
v___x_769_ = l_Lean_MessageData_ofConstName(v_constName_762_, v___x_768_);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__3);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_761_, v___x_772_, v_constName_762_, v___y_763_, v___y_764_, v___y_765_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_ref_774_, lean_object* v_constName_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_774_, v_constName_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec(v_ref_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_ref_786_; lean_object* v___x_787_; 
v_ref_786_ = lean_ctor_get(v___y_783_, 5);
v___x_787_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_786_, v_constName_781_, v___y_782_, v___y_783_, v___y_784_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(lean_object* v_constName_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; lean_object* v_env_800_; uint8_t v___x_801_; lean_object* v___x_802_; 
v___x_799_ = lean_st_ref_get(v___y_797_);
v_env_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc_ref(v_env_800_);
lean_dec(v___x_799_);
v___x_801_ = 0;
lean_inc(v_constName_794_);
v___x_802_ = l_Lean_Environment_findConstVal_x3f(v_env_800_, v_constName_794_, v___x_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_794_, v___y_795_, v___y_796_, v___y_797_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_constName_794_);
v_val_804_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_802_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_val_804_);
lean_dec(v___x_802_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 0);
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_val_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0___boxed(lean_object* v_constName_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
if (lean_obj_tag(v_a_818_) == 0)
{
lean_object* v___x_820_; 
v___x_820_ = l_List_reverse___redArg(v_a_819_);
return v___x_820_;
}
else
{
lean_object* v_head_821_; lean_object* v_tail_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_831_; 
v_head_821_ = lean_ctor_get(v_a_818_, 0);
v_tail_822_ = lean_ctor_get(v_a_818_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_a_818_);
if (v_isSharedCheck_831_ == 0)
{
v___x_824_ = v_a_818_;
v_isShared_825_ = v_isSharedCheck_831_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_tail_822_);
lean_inc(v_head_821_);
lean_dec(v_a_818_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_831_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = l_Lean_mkLevelParam(v_head_821_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v_a_819_);
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_a_819_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_a_818_ = v_tail_822_;
v_a_819_ = v___x_828_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(lean_object* v_constName_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; 
lean_inc(v_constName_832_);
v___x_837_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0(v_constName_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_849_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_849_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_849_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_849_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_levelParams_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v_levelParams_842_ = lean_ctor_get(v_a_838_, 1);
lean_inc(v_levelParams_842_);
lean_dec(v_a_838_);
v___x_843_ = lean_box(0);
v___x_844_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__1(v_levelParams_842_, v___x_843_);
v___x_845_ = l_Lean_mkConst(v_constName_832_, v___x_844_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_845_);
v___x_847_ = v___x_840_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_constName_832_);
v_a_850_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_837_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_837_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0___boxed(lean_object* v_constName_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_constName_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
return v_res_863_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__1));
v___x_870_ = l_Lean_MessageData_ofFormat(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__4));
v___x_875_ = l_Lean_MessageData_ofFormat(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__6));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Key_format___closed__6));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(uint8_t v_parenIfNonAtomic_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_next_x3f___redArg(v_a_882_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_1005_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_1005_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_1005_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
if (lean_obj_tag(v_a_887_) == 1)
{
lean_object* v_val_891_; 
v_val_891_ = lean_ctor_get(v_a_887_, 0);
lean_inc(v_val_891_);
lean_dec_ref(v_a_887_);
switch(lean_obj_tag(v_val_891_))
{
case 0:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__2);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
case 1:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__5);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_896_);
v___x_898_ = v___x_889_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
case 2:
{
lean_object* v_a_900_; 
v_a_900_ = lean_ctor_get(v_val_891_, 0);
lean_inc_ref(v_a_900_);
lean_dec_ref(v_val_891_);
if (lean_obj_tag(v_a_900_) == 0)
{
lean_object* v_val_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_913_; 
v_val_901_ = lean_ctor_get(v_a_900_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_900_);
if (v_isSharedCheck_913_ == 0)
{
v___x_903_ = v_a_900_;
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_val_901_);
lean_dec(v_a_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = l_Nat_reprFast(v_val_901_);
if (v_isShared_904_ == 0)
{
lean_ctor_set_tag(v___x_903_, 3);
lean_ctor_set(v___x_903_, 0, v___x_905_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_912_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = l_Lean_MessageData_ofFormat(v___x_907_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_908_);
v___x_910_ = v___x_889_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_val_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v_val_914_ = lean_ctor_get(v_a_900_, 0);
lean_inc_ref(v_val_914_);
lean_dec_ref(v_a_900_);
v___x_915_ = l_Lean_stringToMessageData(v_val_914_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_915_);
v___x_917_ = v___x_889_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
case 3:
{
lean_object* v_a_919_; lean_object* v_a_920_; lean_object* v___x_921_; 
lean_del_object(v___x_889_);
v_a_919_ = lean_ctor_get(v_val_891_, 0);
lean_inc(v_a_919_);
v_a_920_ = lean_ctor_get(v_val_891_, 1);
lean_inc(v_a_920_);
lean_dec_ref(v_val_891_);
v___x_921_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_920_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v___x_923_ = l_Lean_mkFVar(v_a_919_);
v___x_924_ = l_Lean_MessageData_ofExpr(v___x_923_);
v___x_925_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_924_, v_a_922_, v_parenIfNonAtomic_881_, v_a_883_, v_a_884_);
lean_dec(v_a_922_);
return v___x_925_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_919_);
v_a_926_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_921_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
case 4:
{
lean_object* v_a_934_; lean_object* v_a_935_; lean_object* v___x_936_; 
lean_del_object(v___x_889_);
v_a_934_ = lean_ctor_get(v_val_891_, 0);
lean_inc(v_a_934_);
v_a_935_ = lean_ctor_get(v_val_891_, 1);
lean_inc(v_a_935_);
lean_dec_ref(v_val_891_);
v___x_936_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0(v_a_934_, v_a_882_, v_a_883_, v_a_884_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_935_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_935_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v___x_938_);
v___x_940_ = l_Lean_MessageData_ofExpr(v_a_937_);
v___x_941_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_940_, v_a_939_, v_parenIfNonAtomic_881_, v_a_883_, v_a_884_);
lean_dec(v_a_939_);
return v___x_941_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_a_937_);
v_a_942_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_938_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_938_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v_a_935_);
v_a_950_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_936_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_936_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
case 5:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_del_object(v___x_889_);
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v___x_958_, v_a_882_, v_a_883_, v_a_884_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
v___x_961_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__7);
v___x_962_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_961_, v_a_960_, v_parenIfNonAtomic_881_, v_a_883_, v_a_884_);
lean_dec(v_a_960_);
return v___x_962_;
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_959_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
default: 
{
lean_object* v_a_971_; lean_object* v_a_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
lean_del_object(v___x_889_);
v_a_971_ = lean_ctor_get(v_val_891_, 1);
lean_inc(v_a_971_);
v_a_972_ = lean_ctor_get(v_val_891_, 2);
lean_inc(v_a_972_);
lean_dec_ref(v_val_891_);
v___x_973_ = 1;
v___x_974_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_973_, v_a_882_, v_a_883_, v_a_884_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1000_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_1000_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1000_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; 
v___x_979_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_a_972_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_972_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___closed__8);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v_a_975_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_add(v_a_971_, v___x_983_);
lean_dec(v_a_971_);
v___x_985_ = l_Nat_reprFast(v___x_984_);
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 3);
lean_ctor_set(v___x_977_, 0, v___x_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_991_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = l_Lean_MessageData_ofFormat(v___x_987_);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_982_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_mkApp(v___x_989_, v_a_980_, v_parenIfNonAtomic_881_, v_a_883_, v_a_884_);
lean_dec(v_a_980_);
return v___x_990_;
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_del_object(v___x_977_);
lean_dec(v_a_975_);
lean_dec(v_a_971_);
v_a_992_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_979_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_979_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
else
{
lean_dec(v_a_972_);
lean_dec(v_a_971_);
return v___x_974_;
}
}
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_dec(v_a_887_);
v___x_1001_ = l_Lean_MessageData_nil;
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_1001_);
v___x_1003_ = v___x_889_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_886_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_886_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(lean_object* v_upperBound_1014_, lean_object* v_a_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_lt(v_a_1015_, v_upperBound_1014_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
lean_dec(v_a_1015_);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v_b_1016_);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1021_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = lean_array_push(v_b_1016_, v_a_1024_);
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_a_1015_, v___x_1026_);
lean_dec(v_a_1015_);
v_a_1015_ = v___x_1027_;
v_b_1016_ = v___x_1025_;
goto _start;
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v_b_1016_);
lean_dec(v_a_1015_);
v_a_1029_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1023_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1023_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(lean_object* v_num_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v_r_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_unsigned_to_nat(0u);
v_r_1043_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___closed__0));
v___x_1044_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_num_1037_, v___x_1042_, v_r_1043_, v_a_1038_, v_a_1039_, v_a_1040_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN___boxed(lean_object* v_num_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN(v_num_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec(v_num_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg___boxed(lean_object* v_upperBound_1051_, lean_object* v_a_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_1051_, v_a_1052_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v_upperBound_1051_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go___boxed(lean_object* v_parenIfNonAtomic_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
uint8_t v_parenIfNonAtomic_boxed_1064_; lean_object* v_res_1065_; 
v_parenIfNonAtomic_boxed_1064_ = lean_unbox(v_parenIfNonAtomic_1059_);
v_res_1065_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v_parenIfNonAtomic_boxed_1064_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(lean_object* v_upperBound_1066_, lean_object* v_inst_1067_, lean_object* v_R_1068_, lean_object* v_a_1069_, lean_object* v_b_1070_, lean_object* v_c_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___redArg(v_upperBound_1066_, v_a_1069_, v_b_1070_, v___y_1072_, v___y_1073_, v___y_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2___boxed(lean_object* v_upperBound_1077_, lean_object* v_inst_1078_, lean_object* v_R_1079_, lean_object* v_a_1080_, lean_object* v_b_1081_, lean_object* v_c_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_goN_spec__2(v_upperBound_1077_, v_inst_1078_, v_R_1079_, v_a_1080_, v_b_1081_, v_c_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec(v_upperBound_1077_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1088_, lean_object* v_constName_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___redArg(v_constName_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1095_, lean_object* v_constName_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2(v_00_u03b1_1095_, v_constName_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_1102_, lean_object* v_ref_1103_, lean_object* v_constName_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___redArg(v_ref_1103_, v_constName_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_ref_1111_, lean_object* v_constName_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_1110_, v_ref_1111_, v_constName_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec(v_ref_1111_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1118_, lean_object* v_ref_1119_, lean_object* v_msg_1120_, lean_object* v_declHint_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___redArg(v_ref_1119_, v_msg_1120_, v_declHint_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_ref_1128_, lean_object* v_msg_1129_, lean_object* v_declHint_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6(v_00_u03b1_1127_, v_ref_1128_, v_msg_1129_, v_declHint_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec(v_ref_1128_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_1136_, lean_object* v_declHint_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1136_, v_declHint_1137_, v___y_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_1143_, lean_object* v_declHint_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__7_spec__8(v_msg_1143_, v_declHint_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_1150_, lean_object* v_ref_1151_, lean_object* v_msg_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___redArg(v_ref_1151_, v_msg_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_ref_1159_, lean_object* v_msg_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8(v_00_u03b1_1158_, v_ref_1159_, v_msg_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec(v_ref_1159_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_1166_, lean_object* v_msg_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1167_, v___y_1169_, v___y_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1173_, lean_object* v_msg_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go_spec__0_spec__0_spec__2_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_1173_, v_msg_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern(lean_object* v_keys_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1184_ = lean_array_to_list(v_keys_1180_);
v___x_1185_ = lean_st_mk_ref(v___x_1184_);
v___x_1186_ = 0;
v___x_1187_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_keysAsPattern_go(v___x_1186_, v___x_1185_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_st_ref_get(v___x_1185_);
lean_dec(v___x_1185_);
lean_dec(v___x_1192_);
if (v_isShared_1191_ == 0)
{
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1188_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
lean_dec(v___x_1185_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_keysAsPattern___boxed(lean_object* v_keys_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Meta_DiscrTree_keysAsPattern(v_keys_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object* v_keys_1204_, lean_object* v_v_1205_, lean_object* v_i_1206_){
_start:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_array_get_size(v_keys_1204_);
v___x_1208_ = lean_nat_dec_lt(v_i_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_mk_empty_array_with_capacity(v___x_1209_);
v___x_1211_ = lean_array_push(v___x_1210_, v_v_1205_);
v___x_1212_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___closed__0));
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
return v___x_1213_;
}
else
{
lean_object* v_k_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_c_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_k_1214_ = lean_array_fget_borrowed(v_keys_1204_, v_i_1206_);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_add(v_i_1206_, v___x_1215_);
v_c_1217_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1204_, v_v_1205_, v___x_1216_);
lean_dec(v___x_1216_);
v___x_1218_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__0));
lean_inc(v_k_1214_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_k_1214_);
lean_ctor_set(v___x_1219_, 1, v_c_1217_);
v___x_1220_ = lean_mk_empty_array_with_capacity(v___x_1215_);
v___x_1221_ = lean_array_push(v___x_1220_, v___x_1219_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1218_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg___boxed(lean_object* v_keys_1223_, lean_object* v_v_1224_, lean_object* v_i_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1223_, v_v_1224_, v_i_1225_);
lean_dec(v_i_1225_);
lean_dec_ref(v_keys_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object* v_00_u03b1_1227_, lean_object* v_keys_1228_, lean_object* v_v_1229_, lean_object* v_i_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1228_, v_v_1229_, v_i_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_keys_1233_, lean_object* v_v_1234_, lean_object* v_i_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(v_00_u03b1_1232_, v_keys_1233_, v_v_1234_, v_i_1235_);
lean_dec(v_i_1235_);
lean_dec_ref(v_keys_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(lean_object* v_inst_1237_, lean_object* v_vs_1238_, lean_object* v_v_1239_, lean_object* v_i_1240_){
_start:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_array_get_size(v_vs_1238_);
v___x_1242_ = lean_nat_dec_lt(v_i_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec(v_i_1240_);
lean_dec_ref(v_inst_1237_);
v___x_1243_ = lean_array_push(v_vs_1238_, v_v_1239_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = lean_array_fget_borrowed(v_vs_1238_, v_i_1240_);
lean_inc_ref(v_inst_1237_);
lean_inc(v___x_1244_);
lean_inc(v_v_1239_);
v___x_1245_ = lean_apply_2(v_inst_1237_, v_v_1239_, v___x_1244_);
v___x_1246_ = lean_unbox(v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v_i_1240_, v___x_1247_);
lean_dec(v_i_1240_);
v_i_1240_ = v___x_1248_;
goto _start;
}
else
{
lean_object* v___x_1250_; 
lean_dec_ref(v_inst_1237_);
v___x_1250_ = lean_array_fset(v_vs_1238_, v_i_1240_, v_v_1239_);
lean_dec(v_i_1240_);
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop(lean_object* v_00_u03b1_1251_, lean_object* v_inst_1252_, lean_object* v_vs_1253_, lean_object* v_v_1254_, lean_object* v_i_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(v_inst_1252_, v_vs_1253_, v_v_1254_, v_i_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(lean_object* v_inst_1257_, lean_object* v_vs_1258_, lean_object* v_v_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___redArg(v_inst_1257_, v_vs_1258_, v_v_1259_, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal(lean_object* v_00_u03b1_1262_, lean_object* v_inst_1263_, lean_object* v_vs_1264_, lean_object* v_v_1265_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_1263_, v_vs_1264_, v_v_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(lean_object* v_a_1267_, lean_object* v_b_1268_){
_start:
{
lean_object* v_fst_1269_; lean_object* v_fst_1270_; uint8_t v___x_1271_; 
v_fst_1269_ = lean_ctor_get(v_a_1267_, 0);
v_fst_1270_ = lean_ctor_get(v_b_1268_, 0);
v___x_1271_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1269_, v_fst_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0___boxed(lean_object* v_a_1272_, lean_object* v_b_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__0(v_a_1272_, v_b_1273_);
lean_dec_ref(v_b_1273_);
lean_dec_ref(v_a_1272_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(lean_object* v_x_1276_, lean_object* v_keys_1277_, lean_object* v_v_1278_, lean_object* v_k_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_c_1283_; lean_object* v___x_1284_; 
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_add(v_x_1276_, v___x_1281_);
v_c_1283_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1277_, v_v_1278_, v___x_1282_);
lean_dec(v___x_1282_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_k_1279_);
lean_ctor_set(v___x_1284_, 1, v_c_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed(lean_object* v_x_1285_, lean_object* v_keys_1286_, lean_object* v_v_1287_, lean_object* v_k_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2(v_x_1285_, v_keys_1286_, v_v_1287_, v_k_1288_, v_x_1289_);
lean_dec_ref(v_keys_1286_);
lean_dec(v_x_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed(lean_object* v_x_1292_, lean_object* v_inst_1293_, lean_object* v_keys_1294_, lean_object* v_v_1295_, lean_object* v_k_1296_, lean_object* v_x_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(v_x_1292_, v_inst_1293_, v_keys_1294_, v_v_1295_, v_k_1296_, v_x_1297_);
lean_dec(v_x_1292_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(lean_object* v_inst_1318_, lean_object* v_keys_1319_, lean_object* v_v_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
lean_object* v_vs_1323_; lean_object* v_children_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1345_; 
v_vs_1323_ = lean_ctor_get(v_x_1322_, 0);
v_children_1324_ = lean_ctor_get(v_x_1322_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1326_ = v_x_1322_;
v_isShared_1327_ = v_isSharedCheck_1345_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_children_1324_);
lean_inc(v_vs_1323_);
lean_dec(v_x_1322_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1345_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = lean_array_get_size(v_keys_1319_);
v___x_1329_ = lean_nat_dec_lt(v_x_1321_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
lean_dec(v_x_1321_);
lean_dec_ref(v_keys_1319_);
v___x_1330_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___redArg(v_inst_1318_, v_vs_1323_, v_v_1320_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1330_);
v___x_1332_ = v___x_1326_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_children_1324_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
else
{
lean_object* v___f_1334_; lean_object* v_k_1335_; lean_object* v___f_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_c_1341_; lean_object* v___x_1343_; 
v___f_1334_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__0));
v_k_1335_ = lean_array_fget(v_keys_1319_, v_x_1321_);
lean_inc_n(v_k_1335_, 2);
lean_inc(v_v_1320_);
lean_inc_ref(v_keys_1319_);
lean_inc(v_x_1321_);
v___f_1336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1336_, 0, v_x_1321_);
lean_closure_set(v___f_1336_, 1, v_inst_1318_);
lean_closure_set(v___f_1336_, 2, v_keys_1319_);
lean_closure_set(v___f_1336_, 3, v_v_1320_);
lean_closure_set(v___f_1336_, 4, v_k_1335_);
v___f_1337_ = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1337_, 0, v_x_1321_);
lean_closure_set(v___f_1337_, 1, v_keys_1319_);
lean_closure_set(v___f_1337_, 2, v_v_1320_);
lean_closure_set(v___f_1337_, 3, v_k_1335_);
v___x_1338_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___closed__10));
v___x_1339_ = ((lean_object*)(l_Lean_Meta_DiscrTree_instInhabitedTrie___closed__1));
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v_k_1335_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v_c_1341_ = l_Array_binInsertM___redArg(v___x_1338_, v___f_1334_, v___f_1336_, v___f_1337_, v_children_1324_, v___x_1340_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_c_1341_);
v___x_1343_ = v___x_1326_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_vs_1323_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_c_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg___lam__1(lean_object* v_x_1346_, lean_object* v_inst_1347_, lean_object* v_keys_1348_, lean_object* v_v_1349_, lean_object* v_k_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v_snd_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1362_; 
v_snd_1352_ = lean_ctor_get(v_x_1351_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v_x_1351_, 0);
lean_dec(v_unused_1363_);
v___x_1354_ = v_x_1351_;
v_isShared_1355_ = v_isSharedCheck_1362_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_snd_1352_);
lean_dec(v_x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1362_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_c_1358_; lean_object* v___x_1360_; 
v___x_1356_ = lean_unsigned_to_nat(1u);
v___x_1357_ = lean_nat_add(v_x_1346_, v___x_1356_);
v_c_1358_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1347_, v_keys_1348_, v_v_1349_, v___x_1357_, v_snd_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_c_1358_);
lean_ctor_set(v___x_1354_, 0, v_k_1350_);
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_k_1350_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_c_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux(lean_object* v_00_u03b1_1364_, lean_object* v_inst_1365_, lean_object* v_keys_1366_, lean_object* v_v_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1365_, v_keys_1366_, v_v_1367_, v_x_1368_, v_x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2(void){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_1373_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1377_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__5));
v___x_1378_ = lean_unsigned_to_nat(23u);
v___x_1379_ = lean_unsigned_to_nat(166u);
v___x_1380_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__4));
v___x_1381_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__3));
v___x_1382_ = l_mkPanicMessageWithDecl(v___x_1381_, v___x_1380_, v___x_1379_, v___x_1378_, v___x_1377_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg(lean_object* v_inst_1383_, lean_object* v_d_1384_, lean_object* v_keys_1385_, lean_object* v_v_1386_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = lean_array_get_size(v_keys_1385_);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = lean_nat_dec_eq(v___x_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v_k_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1390_ = lean_box(0);
v_k_1391_ = lean_array_get(v___x_1390_, v_keys_1385_, v___x_1388_);
v___x_1392_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__0));
v___x_1393_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__1));
lean_inc(v_k_1391_);
lean_inc_ref(v_d_1384_);
v___x_1394_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1392_, v___x_1393_, v_d_1384_, v_k_1391_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v___x_1395_; lean_object* v_c_1396_; lean_object* v___x_1397_; 
lean_dec_ref(v_inst_1383_);
v___x_1395_ = lean_unsigned_to_nat(1u);
v_c_1396_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes___redArg(v_keys_1385_, v_v_1386_, v___x_1395_);
lean_dec_ref(v_keys_1385_);
v___x_1397_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1392_, v___x_1393_, v_d_1384_, v_k_1391_, v_c_1396_);
return v___x_1397_;
}
else
{
lean_object* v_val_1398_; lean_object* v___x_1399_; lean_object* v_c_1400_; lean_object* v___x_1401_; 
v_val_1398_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1398_);
lean_dec_ref(v___x_1394_);
v___x_1399_ = lean_unsigned_to_nat(1u);
v_c_1400_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___redArg(v_inst_1383_, v_keys_1385_, v_v_1386_, v___x_1399_, v_val_1398_);
v___x_1401_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1392_, v___x_1393_, v_d_1384_, v_k_1391_, v_c_1400_);
return v___x_1401_;
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_v_1386_);
lean_dec_ref(v_keys_1385_);
lean_dec_ref(v_d_1384_);
lean_dec_ref(v_inst_1383_);
v___x_1402_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2, &l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__2);
v___x_1403_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6, &l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___redArg___closed__6);
v___x_1404_ = l_panic___redArg(v___x_1402_, v___x_1403_);
return v___x_1404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue(lean_object* v_00_u03b1_1405_, lean_object* v_inst_1406_, lean_object* v_d_1407_, lean_object* v_keys_1408_, lean_object* v_v_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_1406_, v_d_1407_, v_keys_1408_, v_v_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___redArg(lean_object* v_inst_1411_, lean_object* v_d_1412_, lean_object* v_keys_1413_, lean_object* v_v_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_1411_, v_d_1412_, v_keys_1413_, v_v_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore(lean_object* v_00_u03b1_1416_, lean_object* v_inst_1417_, lean_object* v_d_1418_, lean_object* v_keys_1419_, lean_object* v_v_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_1417_, v_d_1418_, v_keys_1419_, v_v_1420_);
return v___x_1421_;
}
}
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
