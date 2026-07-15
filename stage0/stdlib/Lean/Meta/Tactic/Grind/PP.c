// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PP
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Util import Init.Grind.Injective import Init.Grind.PP import Lean.Meta.Tactic.Grind.Arith.CommRing.PP import Lean.Meta.Tactic.Grind.Arith.Linear.PP import Lean.Meta.Tactic.Grind.AC.PP import Lean.Meta.Tactic.Grind.CastLike import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode_x3f(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitSource_toMessageData(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_isCastLikeApp(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_Grind_isCastLikeDeclName(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Origin_pp(lean_object*);
lean_object* l_Lean_Meta_Grind_ppPattern(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grind_debug;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getTarget_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqcs(lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Goal_ppENodeRef___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "node_def"};
static const lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 136, 159, 149, 215, 39, 162, 121)}};
static const lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Goal_ppENodeRef___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Goal_ppENodeRef___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__4_value)}};
static const lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↝ "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", [ctor]"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", [val]"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__3_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__6_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__9_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Goal_ppState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Goal:"};
static const lean_object* l_Lean_Meta_Grind_Goal_ppState___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Goal_ppState___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Goal_ppState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Goal_ppState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_ppGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Grind_ppGoals___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_ppGoals___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_ppGoals___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ppGoals___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0;
static const lean_array_object l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1 = (const lean_object*)&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppExprArray(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppExprArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "leftInv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__2_value),LEAN_SCALAR_PTR_LITERAL(125, 193, 128, 144, 122, 197, 27, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 194, 82, 68, 109, 146, 236, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instInhabitedResult_default;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__15_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__21_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_ppEqc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eqc"};
static const lean_object* l_Lean_Meta_Grind_ppEqc___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_ppEqc___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_ppEqc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_ppEqc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 40, 20, 175, 160, 100, 35, 190)}};
static const lean_object* l_Lean_Meta_Grind_ppEqc___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_ppEqc___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_ppEqc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ppEqc___closed__2;
static const lean_string_object l_Lean_Meta_Grind_ppEqc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Meta_Grind_ppEqc___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_ppEqc___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_ppEqc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_ppEqc___closed__3_value)}};
static const lean_object* l_Lean_Meta_Grind_ppEqc___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_ppEqc___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_ppEqc___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ppEqc___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_ppEqc___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_ppEqc___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppEqc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "False propositions"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prop"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(56, 247, 67, 203, 121, 106, 5, 21)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "True propositions"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Equivalence classes"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1_value),((lean_object*)&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "others"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__7_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 106, 229, 125, 19, 158, 75, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ematch"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 93, 194, 130, 184, 168, 50, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "E-matching patterns"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__3_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assign"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 147, 101, 187, 172, 93, 80, 64)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cutsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 214, 139, 23, 110, 35, 174, 214)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Assignment satisfying linear constraints"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__3_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "limits"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 8, 45, 24, 251, 175, 249, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Thresholds reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__3_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "limit"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(202, 254, 210, 223, 64, 235, 83, 93)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "maximum term generation has been reached, threshold: `(gen := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "maximum number of case-splits has been reached, threshold: `(splits := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "maximum number of E-matching rounds has been reached, threshold: `(ematch := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "maximum number of instances generated by E-matching has been reached, threshold: `(instances := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 93, 203, 178, 149, 199, 118, 190)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "source: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Case analyses"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "facts"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 104, 51, 228, 98, 188, 251, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Asserted facts"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_goalDiagToMessageData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_goalDiagToMessageData___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_goalDiagToMessageData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Goal diagnostics"};
static const lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__5));
v___x_12_ = l_Lean_MessageData_ofFormat(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef(lean_object* v_goal_13_, lean_object* v_e_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Meta_Grind_Goal_getENode_x3f(v_goal_13_, v_e_14_);
if (lean_obj_tag(v___x_20_) == 1)
{
lean_object* v_val_21_; lean_object* v___x_22_; 
v_val_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v___x_20_, 1);
lean_inc(v_a_18_);
lean_inc_ref(v_a_17_);
lean_inc(v_a_16_);
lean_inc_ref(v_a_15_);
lean_inc_ref(v_e_14_);
v___x_22_ = lean_infer_type(v_e_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_24_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_n(v_a_23_, 2);
lean_dec_ref_known(v___x_22_, 1);
v___x_24_ = l_Lean_Meta_getLevel(v_a_23_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_40_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_40_ == 0)
{
v___x_27_ = v___x_24_;
v_isShared_28_ = v_isSharedCheck_40_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_40_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_idx_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v_idx_29_ = lean_ctor_get(v_val_21_, 7);
lean_inc(v_idx_29_);
lean_dec(v_val_21_);
v___x_30_ = ((lean_object*)(l_Lean_Meta_Grind_Goal_ppENodeRef___closed__3));
v___x_31_ = lean_box(0);
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v_a_25_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = l_Lean_mkConst(v___x_30_, v___x_32_);
v___x_34_ = l_Lean_mkNatLit(v_idx_29_);
v___x_35_ = l_Lean_mkApp3(v___x_33_, v___x_34_, v_a_23_, v_e_14_);
v___x_36_ = l_Lean_MessageData_ofExpr(v___x_35_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_36_);
v___x_38_ = v___x_27_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
lean_dec(v_a_23_);
lean_dec(v_val_21_);
lean_dec_ref(v_e_14_);
v_a_41_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_24_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_24_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
else
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
lean_dec(v_val_21_);
lean_dec_ref(v_e_14_);
v_a_49_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_22_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_22_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
else
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v___x_20_);
lean_dec_ref(v_e_14_);
v___x_57_ = lean_obj_once(&l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6, &l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6_once, _init_l_Lean_Meta_Grind_Goal_ppENodeRef___closed__6);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppENodeRef___boxed(lean_object* v_goal_59_, lean_object* v_e_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_59_, v_e_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_goal_59_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg(lean_object* v_e_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_st_ref_get(v_a_68_);
v___x_75_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v___x_74_, v_e_67_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg___boxed(lean_object* v_e_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_e_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef(lean_object* v_e_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_e_84_, v_a_85_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef___boxed(lean_object* v_e_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Meta_Grind_ppENodeRef(v_e_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec(v_a_98_);
return v_res_109_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__1));
v___x_114_ = l_Lean_MessageData_ofFormat(v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0(lean_object* v_goal_115_, lean_object* v_as_116_, size_t v_sz_117_, size_t v_i_118_, lean_object* v_b_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_usize_dec_lt(v_i_118_, v_sz_117_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v_b_119_);
return v___x_126_;
}
else
{
lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_127_ = lean_array_uget_borrowed(v_as_116_, v_i_118_);
lean_inc(v_a_127_);
v___x_128_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_115_, v_a_127_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; size_t v___x_133_; size_t v___x_134_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_128_, 1);
v___x_130_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___closed__2);
v___x_131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_131_, 0, v_b_119_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v_a_129_);
v___x_133_ = ((size_t)1ULL);
v___x_134_ = lean_usize_add(v_i_118_, v___x_133_);
v_i_118_ = v___x_134_;
v_b_119_ = v___x_132_;
goto _start;
}
else
{
lean_dec_ref(v_b_119_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0___boxed(lean_object* v_goal_136_, lean_object* v_as_137_, lean_object* v_sz_138_, lean_object* v_i_139_, lean_object* v_b_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
size_t v_sz_boxed_146_; size_t v_i_boxed_147_; lean_object* v_res_148_; 
v_sz_boxed_146_ = lean_unbox_usize(v_sz_138_);
lean_dec(v_sz_138_);
v_i_boxed_147_ = lean_unbox_usize(v_i_139_);
lean_dec(v_i_139_);
v_res_148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0(v_goal_136_, v_as_137_, v_sz_boxed_146_, v_i_boxed_147_, v_b_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec_ref(v_as_137_);
lean_dec_ref(v_goal_136_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1(lean_object* v_goal_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_r_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; 
if (lean_obj_tag(v_x_150_) == 5)
{
lean_object* v_fn_167_; lean_object* v_arg_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_fn_167_ = lean_ctor_get(v_x_150_, 0);
lean_inc_ref(v_fn_167_);
v_arg_168_ = lean_ctor_get(v_x_150_, 1);
lean_inc_ref(v_arg_168_);
lean_dec_ref_known(v_x_150_, 2);
v___x_169_ = lean_array_set(v_x_151_, v_x_152_, v_arg_168_);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_sub(v_x_152_, v___x_170_);
lean_dec(v_x_152_);
v_x_150_ = v_fn_167_;
v_x_151_ = v___x_169_;
v_x_152_ = v___x_171_;
goto _start;
}
else
{
uint8_t v___x_173_; 
lean_dec(v_x_152_);
v___x_173_ = l_Lean_Expr_isConst(v_x_150_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_149_, v_x_150_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
v_r_159_ = v_a_175_;
v___y_160_ = v___y_153_;
v___y_161_ = v___y_154_;
v___y_162_ = v___y_155_;
v___y_163_ = v___y_156_;
goto v___jp_158_;
}
else
{
lean_dec_ref(v_x_151_);
return v___x_174_;
}
}
else
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_MessageData_ofExpr(v_x_150_);
v_r_159_ = v___x_176_;
v___y_160_ = v___y_153_;
v___y_161_ = v___y_154_;
v___y_162_ = v___y_155_;
v___y_163_ = v___y_156_;
goto v___jp_158_;
}
}
v___jp_158_:
{
size_t v_sz_164_; size_t v___x_165_; lean_object* v___x_166_; 
v_sz_164_ = lean_array_size(v_x_151_);
v___x_165_ = ((size_t)0ULL);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__0(v_goal_149_, v_x_151_, v_sz_164_, v___x_165_, v_r_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec_ref(v_x_151_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1___boxed(lean_object* v_goal_177_, lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1(v_goal_177_, v_x_178_, v_x_179_, v_x_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec_ref(v_goal_177_);
return v_res_186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0(void){
_start:
{
lean_object* v___x_187_; lean_object* v_dummy_188_; 
v___x_187_ = lean_box(0);
v_dummy_188_ = l_Lean_Expr_sort___override(v___x_187_);
return v_dummy_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(lean_object* v_goal_189_, lean_object* v_e_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; 
lean_inc_ref(v_e_190_);
v___x_196_ = l_Lean_Meta_isLitValue(v_e_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; uint8_t v___y_218_; uint8_t v___x_225_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_225_ = l_Lean_Expr_isApp(v_e_190_);
if (v___x_225_ == 0)
{
lean_dec(v_a_197_);
v___y_218_ = v___x_225_;
goto v___jp_217_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
if (v___x_226_ == 0)
{
v___y_218_ = v___x_225_;
goto v___jp_217_;
}
else
{
goto v___jp_198_;
}
}
v___jp_198_:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_ppExpr(v_e_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = l_Lean_MessageData_ofFormat(v_a_200_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_209_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_199_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_199_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
v___jp_217_:
{
if (v___y_218_ == 0)
{
goto v___jp_198_;
}
else
{
lean_object* v_dummy_219_; lean_object* v_nargs_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_dummy_219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0);
v_nargs_220_ = l_Lean_Expr_getAppNumArgs(v_e_190_);
lean_inc(v_nargs_220_);
v___x_221_ = lean_mk_array(v_nargs_220_, v_dummy_219_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v_nargs_220_, v___x_222_);
lean_dec(v_nargs_220_);
v___x_224_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1(v_goal_189_, v_e_190_, v___x_221_, v___x_223_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
return v___x_224_;
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v_e_190_);
v_a_227_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_196_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_196_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___boxed(lean_object* v_goal_235_, lean_object* v_e_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(v_goal_235_, v_e_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec_ref(v_goal_235_);
return v_res_242_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(lean_object* v_opts_243_, lean_object* v_opt_244_){
_start:
{
lean_object* v_name_245_; lean_object* v_defValue_246_; lean_object* v_map_247_; lean_object* v___x_248_; 
v_name_245_ = lean_ctor_get(v_opt_244_, 0);
v_defValue_246_ = lean_ctor_get(v_opt_244_, 1);
v_map_247_ = lean_ctor_get(v_opts_243_, 0);
v___x_248_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_247_, v_name_245_);
if (lean_obj_tag(v___x_248_) == 0)
{
uint8_t v___x_249_; 
v___x_249_ = lean_unbox(v_defValue_246_);
return v___x_249_;
}
else
{
lean_object* v_val_250_; 
v_val_250_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_val_250_);
lean_dec_ref_known(v___x_248_, 1);
if (lean_obj_tag(v_val_250_) == 1)
{
uint8_t v_v_251_; 
v_v_251_ = lean_ctor_get_uint8(v_val_250_, 0);
lean_dec_ref_known(v_val_250_, 0);
return v_v_251_;
}
else
{
uint8_t v___x_252_; 
lean_dec(v_val_250_);
v___x_252_ = lean_unbox(v_defValue_246_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0___boxed(lean_object* v_opts_253_, lean_object* v_opt_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(v_opts_253_, v_opt_254_);
lean_dec_ref(v_opt_254_);
lean_dec_ref(v_opts_253_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3));
v___x_264_ = l_Lean_MessageData_ofFormat(v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6));
v___x_269_ = l_Lean_MessageData_ofFormat(v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8));
v___x_272_ = l_Lean_stringToMessageData(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(lean_object* v_goal_276_, lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_r_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___x_308_; 
lean_inc_ref(v_e_277_);
v___x_308_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_276_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_308_, 1);
lean_inc_ref(v_e_277_);
v___x_310_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(v_goal_276_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
lean_inc_ref(v_e_277_);
v___x_312_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_276_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_root_314_; uint8_t v_interpreted_315_; uint8_t v_ctor_316_; lean_object* v_r_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v_r_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; size_t v___x_336_; size_t v___x_337_; uint8_t v___x_338_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v_root_314_ = lean_ctor_get(v_a_313_, 2);
lean_inc_ref(v_root_314_);
v_interpreted_315_ = lean_ctor_get_uint8(v_a_313_, sizeof(void*)*12 + 1);
v_ctor_316_ = lean_ctor_get_uint8(v_a_313_, sizeof(void*)*12 + 2);
lean_dec(v_a_313_);
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v_a_309_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_311_);
v___x_336_ = lean_ptr_addr(v_e_277_);
v___x_337_ = lean_ptr_addr(v_root_314_);
v___x_338_ = lean_usize_dec_eq(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_276_, v_root_314_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_a_340_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_335_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v_r_326_ = v___x_343_;
v___y_327_ = v_a_278_;
v___y_328_ = v_a_279_;
v___y_329_ = v_a_280_;
v___y_330_ = v_a_281_;
goto v___jp_325_;
}
else
{
lean_dec_ref_known(v___x_335_, 2);
lean_dec_ref(v_e_277_);
return v___x_339_;
}
}
else
{
lean_dec_ref(v_root_314_);
v_r_326_ = v___x_335_;
v___y_327_ = v_a_278_;
v___y_328_ = v_a_279_;
v___y_329_ = v_a_280_;
v___y_330_ = v_a_281_;
goto v___jp_325_;
}
v___jp_317_:
{
if (v_ctor_316_ == 0)
{
v_r_284_ = v_r_318_;
v___y_285_ = v___y_319_;
v___y_286_ = v___y_320_;
v___y_287_ = v___y_321_;
v___y_288_ = v___y_322_;
goto v___jp_283_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v_r_318_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v_r_284_ = v___x_324_;
v___y_285_ = v___y_319_;
v___y_286_ = v___y_320_;
v___y_287_ = v___y_321_;
v___y_288_ = v___y_322_;
goto v___jp_283_;
}
}
v___jp_325_:
{
if (v_interpreted_315_ == 0)
{
v_r_318_ = v_r_326_;
v___y_319_ = v___y_327_;
v___y_320_ = v___y_328_;
v___y_321_ = v___y_329_;
v___y_322_ = v___y_330_;
goto v___jp_317_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v_r_326_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v_r_318_ = v___x_332_;
v___y_319_ = v___y_327_;
v___y_320_ = v___y_328_;
v___y_321_ = v___y_329_;
v___y_322_ = v___y_330_;
goto v___jp_317_;
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_a_311_);
lean_dec(v_a_309_);
lean_dec_ref(v_e_277_);
v_a_344_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_312_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_312_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_dec(v_a_309_);
lean_dec_ref(v_e_277_);
return v___x_310_;
}
}
else
{
lean_dec_ref(v_e_277_);
return v___x_308_;
}
v___jp_283_:
{
lean_object* v_options_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_options_289_ = lean_ctor_get(v___y_287_, 2);
v___x_290_ = l_Lean_Meta_Grind_grind_debug;
v___x_291_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(v_options_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
lean_dec_ref(v_e_277_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v_r_284_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v_goal_276_, v_e_277_);
lean_dec_ref(v_e_277_);
if (lean_obj_tag(v___x_293_) == 1)
{
lean_object* v_val_294_; lean_object* v___x_295_; 
v_val_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v___x_293_, 1);
v___x_295_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_276_, v_val_294_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_306_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_306_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_306_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_306_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_a_296_);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v_r_284_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_302_);
v___x_304_ = v___x_298_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_dec_ref(v_r_284_);
return v___x_295_;
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v___x_293_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v_r_284_);
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___boxed(lean_object* v_goal_352_, lean_object* v_e_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_352_, v_e_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_goal_352_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(lean_object* v_goal_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = l_List_reverse___redArg(v_x_362_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
else
{
lean_object* v_head_370_; lean_object* v_tail_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_389_; 
v_head_370_ = lean_ctor_get(v_x_361_, 0);
v_tail_371_ = lean_ctor_get(v_x_361_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_361_);
if (v_isSharedCheck_389_ == 0)
{
v___x_373_ = v_x_361_;
v_isShared_374_ = v_isSharedCheck_389_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_tail_371_);
lean_inc(v_head_370_);
lean_dec(v_x_361_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_389_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_360_, v_head_370_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_375_, 1);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 1, v_x_362_);
lean_ctor_set(v___x_373_, 0, v_a_376_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_376_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_x_362_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
v_x_361_ = v_tail_371_;
v_x_362_ = v___x_378_;
goto _start;
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_del_object(v___x_373_);
lean_dec(v_tail_371_);
lean_dec(v_x_362_);
v_a_381_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_375_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_375_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0___boxed(lean_object* v_goal_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(v_goal_390_, v_x_391_, v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec_ref(v_goal_390_);
return v_res_398_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1));
v___x_403_ = l_Lean_MessageData_ofFormat(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4));
v___x_408_ = l_Lean_MessageData_ofFormat(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7));
v___x_413_ = l_Lean_MessageData_ofFormat(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10));
v___x_418_ = l_Lean_MessageData_ofFormat(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(lean_object* v_goal_419_, lean_object* v_as_x27_420_, lean_object* v_b_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
if (lean_obj_tag(v_as_x27_420_) == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v_b_421_);
return v___x_427_;
}
else
{
lean_object* v_head_428_; lean_object* v_tail_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_head_428_ = lean_ctor_get(v_as_x27_420_, 0);
v_tail_429_ = lean_ctor_get(v_as_x27_420_, 1);
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = l_List_lengthTR___redArg(v_head_428_);
v___x_432_ = lean_nat_dec_lt(v___x_430_, v___x_431_);
lean_dec(v___x_431_);
if (v___x_432_ == 0)
{
v_as_x27_420_ = v_tail_429_;
goto _start;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_box(0);
lean_inc(v_head_428_);
v___x_435_ = l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(v_goal_419_, v_head_428_, v___x_434_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v_b_421_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8);
v___x_442_ = l_Lean_MessageData_joinSep(v_a_436_, v___x_441_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_440_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v_as_x27_420_ = v_tail_429_;
v_b_421_ = v___x_445_;
goto _start;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v_b_421_);
v_a_447_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_435_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_435_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___boxed(lean_object* v_goal_455_, lean_object* v_as_x27_456_, lean_object* v_b_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_455_, v_as_x27_456_, v_b_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v_as_x27_456_);
lean_dec_ref(v_goal_455_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(lean_object* v_goal_464_, lean_object* v_as_465_, size_t v_sz_466_, size_t v_i_467_, lean_object* v_b_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = lean_usize_dec_lt(v_i_467_, v_sz_466_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v_b_468_);
return v___x_475_;
}
else
{
lean_object* v_snd_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_512_; 
v_snd_476_ = lean_ctor_get(v_b_468_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_b_468_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v_b_468_, 0);
lean_dec(v_unused_513_);
v___x_478_ = v_b_468_;
v_isShared_479_ = v_isSharedCheck_512_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_snd_476_);
lean_dec(v_b_468_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_512_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_a_480_; lean_object* v___x_481_; 
v_a_480_ = lean_array_uget_borrowed(v_as_465_, v_i_467_);
lean_inc(v_a_480_);
v___x_481_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_464_, v_a_480_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v_self_483_; lean_object* v___x_484_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_481_, 1);
v_self_483_ = lean_ctor_get(v_a_482_, 0);
lean_inc_ref(v_self_483_);
lean_dec(v_a_482_);
v___x_484_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_464_, v_self_483_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = lean_box(0);
v___x_487_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v_snd_476_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_a_485_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_489_);
lean_ctor_set(v___x_478_, 0, v___x_486_);
v___x_491_ = v___x_478_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
size_t v___x_492_; size_t v___x_493_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_467_, v___x_492_);
v_i_467_ = v___x_493_;
v_b_468_ = v___x_491_;
goto _start;
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_del_object(v___x_478_);
lean_dec(v_snd_476_);
v_a_496_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_484_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_484_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_del_object(v___x_478_);
lean_dec(v_snd_476_);
v_a_504_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_481_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_481_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_goal_514_, lean_object* v_as_515_, lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_b_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
size_t v_sz_boxed_524_; size_t v_i_boxed_525_; lean_object* v_res_526_; 
v_sz_boxed_524_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_525_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(v_goal_514_, v_as_515_, v_sz_boxed_524_, v_i_boxed_525_, v_b_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_as_515_);
lean_dec_ref(v_goal_514_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(lean_object* v_goal_527_, lean_object* v_as_528_, size_t v_sz_529_, size_t v_i_530_, lean_object* v_b_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = lean_usize_dec_lt(v_i_530_, v_sz_529_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_b_531_);
return v___x_538_;
}
else
{
lean_object* v_snd_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_575_; 
v_snd_539_ = lean_ctor_get(v_b_531_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_b_531_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_b_531_, 0);
lean_dec(v_unused_576_);
v___x_541_ = v_b_531_;
v_isShared_542_ = v_isSharedCheck_575_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_snd_539_);
lean_dec(v_b_531_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_575_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_a_543_; lean_object* v___x_544_; 
v_a_543_ = lean_array_uget_borrowed(v_as_528_, v_i_530_);
lean_inc(v_a_543_);
v___x_544_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_527_, v_a_543_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v_self_546_; lean_object* v___x_547_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v_self_546_ = lean_ctor_get(v_a_545_, 0);
lean_inc_ref(v_self_546_);
lean_dec(v_a_545_);
v___x_547_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_527_, v_self_546_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = lean_box(0);
v___x_550_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v_snd_539_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_a_548_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_552_);
lean_ctor_set(v___x_541_, 0, v___x_549_);
v___x_554_ = v___x_541_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_530_, v___x_555_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(v_goal_527_, v_as_528_, v_sz_529_, v___x_556_, v___x_554_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_557_;
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_del_object(v___x_541_);
lean_dec(v_snd_539_);
v_a_559_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_547_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_547_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_del_object(v___x_541_);
lean_dec(v_snd_539_);
v_a_567_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_544_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_544_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3___boxed(lean_object* v_goal_577_, lean_object* v_as_578_, lean_object* v_sz_579_, lean_object* v_i_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
size_t v_sz_boxed_587_; size_t v_i_boxed_588_; lean_object* v_res_589_; 
v_sz_boxed_587_ = lean_unbox_usize(v_sz_579_);
lean_dec(v_sz_579_);
v_i_boxed_588_ = lean_unbox_usize(v_i_580_);
lean_dec(v_i_580_);
v_res_589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(v_goal_577_, v_as_578_, v_sz_boxed_587_, v_i_boxed_588_, v_b_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec_ref(v_as_578_);
lean_dec_ref(v_goal_577_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(lean_object* v_init_590_, lean_object* v_goal_591_, lean_object* v_n_592_, lean_object* v_b_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
if (lean_obj_tag(v_n_592_) == 0)
{
lean_object* v_cs_599_; lean_object* v___x_600_; lean_object* v___x_601_; size_t v_sz_602_; size_t v___x_603_; lean_object* v___x_604_; 
v_cs_599_ = lean_ctor_get(v_n_592_, 0);
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_b_593_);
v_sz_602_ = lean_array_size(v_cs_599_);
v___x_603_ = ((size_t)0ULL);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(v_init_590_, v_goal_591_, v_cs_599_, v_sz_602_, v___x_603_, v___x_601_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_619_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_619_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_fst_609_; 
v_fst_609_ = lean_ctor_get(v_a_605_, 0);
if (lean_obj_tag(v_fst_609_) == 0)
{
lean_object* v_snd_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v_snd_610_ = lean_ctor_get(v_a_605_, 1);
lean_inc(v_snd_610_);
lean_dec(v_a_605_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_snd_610_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_611_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
else
{
lean_object* v_val_615_; lean_object* v___x_617_; 
lean_inc_ref(v_fst_609_);
lean_dec(v_a_605_);
v_val_615_ = lean_ctor_get(v_fst_609_, 0);
lean_inc(v_val_615_);
lean_dec_ref_known(v_fst_609_, 1);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_val_615_);
v___x_617_ = v___x_607_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_val_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_a_620_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_604_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_604_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_object* v_vs_628_; lean_object* v___x_629_; lean_object* v___x_630_; size_t v_sz_631_; size_t v___x_632_; lean_object* v___x_633_; 
v_vs_628_ = lean_ctor_get(v_n_592_, 0);
v___x_629_ = lean_box(0);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_b_593_);
v_sz_631_ = lean_array_size(v_vs_628_);
v___x_632_ = ((size_t)0ULL);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(v_goal_591_, v_vs_628_, v_sz_631_, v___x_632_, v___x_630_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_648_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_648_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_648_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_648_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_fst_638_; 
v_fst_638_ = lean_ctor_get(v_a_634_, 0);
if (lean_obj_tag(v_fst_638_) == 0)
{
lean_object* v_snd_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v_snd_639_ = lean_ctor_get(v_a_634_, 1);
lean_inc(v_snd_639_);
lean_dec(v_a_634_);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v_snd_639_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_640_);
v___x_642_ = v___x_636_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
else
{
lean_object* v_val_644_; lean_object* v___x_646_; 
lean_inc_ref(v_fst_638_);
lean_dec(v_a_634_);
v_val_644_ = lean_ctor_get(v_fst_638_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v_fst_638_, 1);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_val_644_);
v___x_646_ = v___x_636_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_val_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
v_a_649_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_633_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_633_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(lean_object* v_init_657_, lean_object* v_goal_658_, lean_object* v_as_659_, size_t v_sz_660_, size_t v_i_661_, lean_object* v_b_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = lean_usize_dec_lt(v_i_661_, v_sz_660_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v_b_662_);
return v___x_669_;
}
else
{
lean_object* v_snd_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_704_; 
v_snd_670_ = lean_ctor_get(v_b_662_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_b_662_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_b_662_, 0);
lean_dec(v_unused_705_);
v___x_672_ = v_b_662_;
v_isShared_673_ = v_isSharedCheck_704_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_snd_670_);
lean_dec(v_b_662_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_704_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_array_uget_borrowed(v_as_659_, v_i_661_);
lean_inc(v_snd_670_);
v___x_675_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_657_, v_goal_658_, v_a_674_, v_snd_670_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_695_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_695_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_695_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_695_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
if (lean_obj_tag(v_a_676_) == 0)
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v_a_676_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_680_);
v___x_682_ = v___x_672_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_snd_670_);
v___x_682_ = v_reuseFailAlloc_686_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_684_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_682_);
v___x_684_ = v___x_678_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
lean_del_object(v___x_678_);
lean_dec(v_snd_670_);
v_a_687_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v_a_676_, 1);
v___x_688_ = lean_box(0);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v_a_687_);
lean_ctor_set(v___x_672_, 0, v___x_688_);
v___x_690_ = v___x_672_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_a_687_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
size_t v___x_691_; size_t v___x_692_; 
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_661_, v___x_691_);
v_i_661_ = v___x_692_;
v_b_662_ = v___x_690_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_del_object(v___x_672_);
lean_dec(v_snd_670_);
v_a_696_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_675_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_675_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2___boxed(lean_object* v_init_706_, lean_object* v_goal_707_, lean_object* v_as_708_, lean_object* v_sz_709_, lean_object* v_i_710_, lean_object* v_b_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
size_t v_sz_boxed_717_; size_t v_i_boxed_718_; lean_object* v_res_719_; 
v_sz_boxed_717_ = lean_unbox_usize(v_sz_709_);
lean_dec(v_sz_709_);
v_i_boxed_718_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(v_init_706_, v_goal_707_, v_as_708_, v_sz_boxed_717_, v_i_boxed_718_, v_b_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v_as_708_);
lean_dec_ref(v_goal_707_);
lean_dec_ref(v_init_706_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1___boxed(lean_object* v_init_720_, lean_object* v_goal_721_, lean_object* v_n_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_720_, v_goal_721_, v_n_722_, v_b_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec_ref(v_n_722_);
lean_dec_ref(v_goal_721_);
lean_dec_ref(v_init_720_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(lean_object* v_goal_730_, lean_object* v_as_731_, size_t v_sz_732_, size_t v_i_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = lean_usize_dec_lt(v_i_733_, v_sz_732_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_b_734_);
return v___x_741_;
}
else
{
lean_object* v_snd_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_778_; 
v_snd_742_ = lean_ctor_get(v_b_734_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_b_734_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_b_734_, 0);
lean_dec(v_unused_779_);
v___x_744_ = v_b_734_;
v_isShared_745_ = v_isSharedCheck_778_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snd_742_);
lean_dec(v_b_734_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_778_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_746_ = lean_array_uget_borrowed(v_as_731_, v_i_733_);
lean_inc(v_a_746_);
v___x_747_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_730_, v_a_746_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_self_749_; lean_object* v___x_750_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v_self_749_ = lean_ctor_get(v_a_748_, 0);
lean_inc_ref(v_self_749_);
lean_dec(v_a_748_);
v___x_750_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_730_, v_self_749_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
v___x_752_ = lean_box(0);
v___x_753_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v_snd_742_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_a_751_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_755_);
lean_ctor_set(v___x_744_, 0, v___x_752_);
v___x_757_ = v___x_744_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
size_t v___x_758_; size_t v___x_759_; 
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_733_, v___x_758_);
v_i_733_ = v___x_759_;
v_b_734_ = v___x_757_;
goto _start;
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_del_object(v___x_744_);
lean_dec(v_snd_742_);
v_a_762_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_750_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_750_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_744_);
lean_dec(v_snd_742_);
v_a_770_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_747_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_747_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5___boxed(lean_object* v_goal_780_, lean_object* v_as_781_, lean_object* v_sz_782_, lean_object* v_i_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
size_t v_sz_boxed_790_; size_t v_i_boxed_791_; lean_object* v_res_792_; 
v_sz_boxed_790_ = lean_unbox_usize(v_sz_782_);
lean_dec(v_sz_782_);
v_i_boxed_791_ = lean_unbox_usize(v_i_783_);
lean_dec(v_i_783_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(v_goal_780_, v_as_781_, v_sz_boxed_790_, v_i_boxed_791_, v_b_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v_as_781_);
lean_dec_ref(v_goal_780_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(lean_object* v_goal_793_, lean_object* v_as_794_, size_t v_sz_795_, size_t v_i_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_796_, v_sz_795_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_b_797_);
return v___x_804_;
}
else
{
lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_841_; 
v_snd_805_ = lean_ctor_get(v_b_797_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_b_797_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v_b_797_, 0);
lean_dec(v_unused_842_);
v___x_807_ = v_b_797_;
v_isShared_808_ = v_isSharedCheck_841_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_dec(v_b_797_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_841_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_a_809_; lean_object* v___x_810_; 
v_a_809_ = lean_array_uget_borrowed(v_as_794_, v_i_796_);
lean_inc(v_a_809_);
v___x_810_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_793_, v_a_809_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v_self_812_; lean_object* v___x_813_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v_self_812_ = lean_ctor_get(v_a_811_, 0);
lean_inc_ref(v_self_812_);
lean_dec(v_a_811_);
v___x_813_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_793_, v_self_812_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
v___x_815_ = lean_box(0);
v___x_816_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v_snd_805_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_a_814_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_818_);
lean_ctor_set(v___x_807_, 0, v___x_815_);
v___x_820_ = v___x_807_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_818_);
v___x_820_ = v_reuseFailAlloc_824_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_796_, v___x_821_);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(v_goal_793_, v_as_794_, v_sz_795_, v___x_822_, v___x_820_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_823_;
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_del_object(v___x_807_);
lean_dec(v_snd_805_);
v_a_825_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_813_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_813_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_del_object(v___x_807_);
lean_dec(v_snd_805_);
v_a_833_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_810_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_810_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2___boxed(lean_object* v_goal_843_, lean_object* v_as_844_, lean_object* v_sz_845_, lean_object* v_i_846_, lean_object* v_b_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
size_t v_sz_boxed_853_; size_t v_i_boxed_854_; lean_object* v_res_855_; 
v_sz_boxed_853_ = lean_unbox_usize(v_sz_845_);
lean_dec(v_sz_845_);
v_i_boxed_854_ = lean_unbox_usize(v_i_846_);
lean_dec(v_i_846_);
v_res_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(v_goal_843_, v_as_844_, v_sz_boxed_853_, v_i_boxed_854_, v_b_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v_as_844_);
lean_dec_ref(v_goal_843_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(lean_object* v_goal_856_, lean_object* v_t_857_, lean_object* v_init_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_root_864_; lean_object* v_tail_865_; lean_object* v___x_866_; 
v_root_864_ = lean_ctor_get(v_t_857_, 0);
v_tail_865_ = lean_ctor_get(v_t_857_, 1);
lean_inc_ref(v_init_858_);
v___x_866_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_858_, v_goal_856_, v_root_864_, v_init_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec_ref(v_init_858_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_903_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_903_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_903_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_903_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_a_867_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; 
v_a_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v_a_867_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_a_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; size_t v_sz_878_; size_t v___x_879_; lean_object* v___x_880_; 
lean_del_object(v___x_869_);
v_a_875_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v_a_867_, 1);
v___x_876_ = lean_box(0);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v_a_875_);
v_sz_878_ = lean_array_size(v_tail_865_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(v_goal_856_, v_tail_865_, v_sz_878_, v___x_879_, v___x_877_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_894_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_894_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_894_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_894_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_fst_885_; 
v_fst_885_ = lean_ctor_get(v_a_881_, 0);
if (lean_obj_tag(v_fst_885_) == 0)
{
lean_object* v_snd_886_; lean_object* v___x_888_; 
v_snd_886_ = lean_ctor_get(v_a_881_, 1);
lean_inc(v_snd_886_);
lean_dec(v_a_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_snd_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_snd_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
lean_object* v_val_890_; lean_object* v___x_892_; 
lean_inc_ref(v_fst_885_);
lean_dec(v_a_881_);
v_val_890_ = lean_ctor_get(v_fst_885_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v_fst_885_, 1);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_val_890_);
v___x_892_ = v___x_883_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_val_890_);
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
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_880_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_880_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
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
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_904_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_866_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_866_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1___boxed(lean_object* v_goal_912_, lean_object* v_t_913_, lean_object* v_init_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(v_goal_912_, v_t_913_, v_init_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec_ref(v_t_913_);
lean_dec_ref(v_goal_912_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Goal_ppState___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v_r_923_; 
v___x_922_ = ((lean_object*)(l_Lean_Meta_Grind_Goal_ppState___closed__0));
v_r_923_ = l_Lean_stringToMessageData(v___x_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object* v_goal_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_toGoalState_930_; lean_object* v_exprs_931_; lean_object* v_r_932_; lean_object* v___x_933_; 
v_toGoalState_930_ = lean_ctor_get(v_goal_924_, 0);
v_exprs_931_ = lean_ctor_get(v_toGoalState_930_, 2);
v_r_932_ = lean_obj_once(&l_Lean_Meta_Grind_Goal_ppState___closed__1, &l_Lean_Meta_Grind_Goal_ppState___closed__1_once, _init_l_Lean_Meta_Grind_Goal_ppState___closed__1);
v___x_933_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(v_goal_924_, v_exprs_931_, v_r_932_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v___x_935_ = 1;
v___x_936_ = l_Lean_Meta_Grind_Goal_getEqcs(v_goal_924_, v___x_935_);
v___x_937_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_924_, v___x_936_, v_a_934_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v___x_936_);
return v___x_937_;
}
else
{
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppState___boxed(lean_object* v_goal_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Grind_Goal_ppState(v_goal_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec_ref(v_goal_938_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(lean_object* v_goal_945_, lean_object* v_as_946_, lean_object* v_as_x27_947_, lean_object* v_b_948_, lean_object* v_a_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_945_, v_as_x27_947_, v_b_948_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___boxed(lean_object* v_goal_956_, lean_object* v_as_957_, lean_object* v_as_x27_958_, lean_object* v_b_959_, lean_object* v_a_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(v_goal_956_, v_as_957_, v_as_x27_958_, v_b_959_, v_a_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v_as_x27_958_);
lean_dec(v_as_957_);
lean_dec_ref(v_goal_956_);
return v_res_966_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_box(1);
v___x_968_ = l_Lean_MessageData_ofFormat(v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(lean_object* v_as_x27_969_, lean_object* v_b_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
if (lean_obj_tag(v_as_x27_969_) == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v_b_970_);
return v___x_976_;
}
else
{
lean_object* v_head_977_; lean_object* v_tail_978_; lean_object* v___x_979_; 
v_head_977_ = lean_ctor_get(v_as_x27_969_, 0);
v_tail_978_ = lean_ctor_get(v_as_x27_969_, 1);
v___x_979_ = l_Lean_Meta_Grind_Goal_ppState(v_head_977_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v_b_970_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v_a_980_);
v_as_x27_969_ = v_tail_978_;
v_b_970_ = v___x_983_;
goto _start;
}
else
{
lean_dec_ref(v_b_970_);
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___boxed(lean_object* v_as_x27_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_as_x27_985_, v_b_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v_as_x27_985_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v_r_995_; 
v___x_994_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v_r_995_ = l_Lean_stringToMessageData(v___x_994_);
return v_r_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppGoals(lean_object* v_goals_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_r_1002_; lean_object* v___x_1003_; 
v_r_1002_ = lean_obj_once(&l_Lean_Meta_Grind_ppGoals___closed__1, &l_Lean_Meta_Grind_ppGoals___closed__1_once, _init_l_Lean_Meta_Grind_ppGoals___closed__1);
v___x_1003_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_goals_996_, v_r_1002_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppGoals___boxed(lean_object* v_goals_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Meta_Grind_ppGoals(v_goals_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_goals_1004_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(lean_object* v_as_1011_, lean_object* v_as_x27_1012_, lean_object* v_b_1013_, lean_object* v_a_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_as_x27_1012_, v_b_1013_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___boxed(lean_object* v_as_1021_, lean_object* v_as_x27_1022_, lean_object* v_b_1023_, lean_object* v_a_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(v_as_1021_, v_as_x27_1022_, v_b_1023_, v_a_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v_as_x27_1022_);
lean_dec(v_as_1021_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(lean_object* v_m_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_array_push(v_a_1032_, v_m_1031_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg___boxed(lean_object* v_m_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_m_1038_, v_a_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(lean_object* v_m_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_m_1042_, v_a_1044_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___boxed(lean_object* v_m_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(v_m_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_a_1052_);
return v_res_1059_;
}
}
static double _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1060_; double v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_float_of_nat(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(lean_object* v_e_1064_, lean_object* v_cls_1065_){
_start:
{
lean_object* v___x_1066_; double v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1068_ = 1;
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1070_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1070_, 0, v_cls_1065_);
lean_ctor_set(v___x_1070_, 1, v___x_1066_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
lean_ctor_set_float(v___x_1070_, sizeof(void*)*3, v___x_1067_);
lean_ctor_set_float(v___x_1070_, sizeof(void*)*3 + 8, v___x_1067_);
lean_ctor_set_uint8(v___x_1070_, sizeof(void*)*3 + 16, v___x_1068_);
v___x_1071_ = l_Lean_MessageData_ofExpr(v_e_1064_);
v___x_1072_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1073_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1070_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
lean_ctor_set(v___x_1073_, 2, v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(lean_object* v_clsElem_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_bs_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1078_ == 0)
{
lean_dec(v_clsElem_1074_);
return v_bs_1077_;
}
else
{
lean_object* v_v_1079_; lean_object* v___x_1080_; lean_object* v_bs_x27_1081_; lean_object* v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v_v_1079_ = lean_array_uget(v_bs_1077_, v_i_1076_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v_bs_x27_1081_ = lean_array_uset(v_bs_1077_, v_i_1076_, v___x_1080_);
lean_inc(v_clsElem_1074_);
v___x_1082_ = l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(v_v_1079_, v_clsElem_1074_);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1076_, v___x_1083_);
v___x_1085_ = lean_array_uset(v_bs_x27_1081_, v_i_1076_, v___x_1082_);
v_i_1076_ = v___x_1084_;
v_bs_1077_ = v___x_1085_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1___boxed(lean_object* v_clsElem_1087_, lean_object* v_sz_1088_, lean_object* v_i_1089_, lean_object* v_bs_1090_){
_start:
{
size_t v_sz_boxed_1091_; size_t v_i_boxed_1092_; lean_object* v_res_1093_; 
v_sz_boxed_1091_ = lean_unbox_usize(v_sz_1088_);
lean_dec(v_sz_1088_);
v_i_boxed_1092_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(v_clsElem_1087_, v_sz_boxed_1091_, v_i_boxed_1092_, v_bs_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppExprArray(lean_object* v_cls_1094_, lean_object* v_header_1095_, lean_object* v_es_1096_, lean_object* v_clsElem_1097_, uint8_t v_collapsed_1098_){
_start:
{
size_t v_sz_1099_; size_t v___x_1100_; lean_object* v_es_1101_; lean_object* v___x_1102_; double v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_sz_1099_ = lean_array_size(v_es_1096_);
v___x_1100_ = ((size_t)0ULL);
v_es_1101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(v_clsElem_1097_, v_sz_1099_, v___x_1100_, v_es_1096_);
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1104_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1105_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1105_, 0, v_cls_1094_);
lean_ctor_set(v___x_1105_, 1, v___x_1102_);
lean_ctor_set(v___x_1105_, 2, v___x_1104_);
lean_ctor_set_float(v___x_1105_, sizeof(void*)*3, v___x_1103_);
lean_ctor_set_float(v___x_1105_, sizeof(void*)*3 + 8, v___x_1103_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*3 + 16, v_collapsed_1098_);
v___x_1106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_header_1095_);
v___x_1107_ = l_Lean_MessageData_ofFormat(v___x_1106_);
v___x_1108_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1105_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
lean_ctor_set(v___x_1108_, 2, v_es_1101_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppExprArray___boxed(lean_object* v_cls_1109_, lean_object* v_header_1110_, lean_object* v_es_1111_, lean_object* v_clsElem_1112_, lean_object* v_collapsed_1113_){
_start:
{
uint8_t v_collapsed_boxed_1114_; lean_object* v_res_1115_; 
v_collapsed_boxed_1114_ = lean_unbox(v_collapsed_1113_);
v_res_1115_ = l_Lean_Meta_Grind_ppExprArray(v_cls_1109_, v_header_1110_, v_es_1111_, v_clsElem_1112_, v_collapsed_boxed_1114_);
return v_res_1115_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(lean_object* v_declName_1126_){
_start:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1));
v___x_1128_ = lean_name_eq(v_declName_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3));
v___x_1130_ = lean_name_eq(v_declName_1126_, v___x_1129_);
return v___x_1130_;
}
else
{
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___boxed(lean_object* v_declName_1131_){
_start:
{
uint8_t v_res_1132_; lean_object* v_r_1133_; 
v_res_1132_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(v_declName_1131_);
lean_dec(v_declName_1131_);
v_r_1133_ = lean_box(v_res_1132_);
return v_r_1133_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(lean_object* v_declName_1143_){
_start:
{
uint8_t v___y_1145_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3));
v___x_1149_ = lean_name_eq(v_declName_1143_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5));
v___x_1151_ = lean_name_eq(v_declName_1143_, v___x_1150_);
v___y_1145_ = v___x_1151_;
goto v___jp_1144_;
}
else
{
v___y_1145_ = v___x_1149_;
goto v___jp_1144_;
}
v___jp_1144_:
{
if (v___y_1145_ == 0)
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1));
v___x_1147_ = lean_name_eq(v_declName_1143_, v___x_1146_);
return v___x_1147_;
}
else
{
return v___y_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___boxed(lean_object* v_declName_1152_){
_start:
{
uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_res_1153_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_1152_);
lean_dec(v_declName_1152_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(uint8_t v_x_1155_){
_start:
{
switch(v_x_1155_)
{
case 0:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
return v___x_1156_;
}
case 1:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
return v___x_1157_;
}
default: 
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_unsigned_to_nat(2u);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___boxed(lean_object* v_x_1159_){
_start:
{
uint8_t v_x_boxed_1160_; lean_object* v_res_1161_; 
v_x_boxed_1160_ = lean_unbox(v_x_1159_);
v_res_1161_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(v_x_boxed_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(uint8_t v_x_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(v_x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx___boxed(lean_object* v_x_1164_){
_start:
{
uint8_t v_x_4__boxed_1165_; lean_object* v_res_1166_; 
v_x_4__boxed_1165_ = lean_unbox(v_x_1164_);
v_res_1166_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(v_x_4__boxed_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(lean_object* v_k_1167_){
_start:
{
lean_inc(v_k_1167_);
return v_k_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg___boxed(lean_object* v_k_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(v_k_1168_);
lean_dec(v_k_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(lean_object* v_motive_1170_, lean_object* v_ctorIdx_1171_, uint8_t v_t_1172_, lean_object* v_h_1173_, lean_object* v_k_1174_){
_start:
{
lean_inc(v_k_1174_);
return v_k_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___boxed(lean_object* v_motive_1175_, lean_object* v_ctorIdx_1176_, lean_object* v_t_1177_, lean_object* v_h_1178_, lean_object* v_k_1179_){
_start:
{
uint8_t v_t_boxed_1180_; lean_object* v_res_1181_; 
v_t_boxed_1180_ = lean_unbox(v_t_1177_);
v_res_1181_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(v_motive_1175_, v_ctorIdx_1176_, v_t_boxed_1180_, v_h_1178_, v_k_1179_);
lean_dec(v_k_1179_);
lean_dec(v_ctorIdx_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(lean_object* v_num_1182_){
_start:
{
lean_inc(v_num_1182_);
return v_num_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg___boxed(lean_object* v_num_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(v_num_1183_);
lean_dec(v_num_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(lean_object* v_motive_1185_, uint8_t v_t_1186_, lean_object* v_h_1187_, lean_object* v_num_1188_){
_start:
{
lean_inc(v_num_1188_);
return v_num_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___boxed(lean_object* v_motive_1189_, lean_object* v_t_1190_, lean_object* v_h_1191_, lean_object* v_num_1192_){
_start:
{
uint8_t v_t_boxed_1193_; lean_object* v_res_1194_; 
v_t_boxed_1193_ = lean_unbox(v_t_1190_);
v_res_1194_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(v_motive_1189_, v_t_boxed_1193_, v_h_1191_, v_num_1192_);
lean_dec(v_num_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(lean_object* v_cast_1195_){
_start:
{
lean_inc(v_cast_1195_);
return v_cast_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg___boxed(lean_object* v_cast_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(v_cast_1196_);
lean_dec(v_cast_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(lean_object* v_motive_1198_, uint8_t v_t_1199_, lean_object* v_h_1200_, lean_object* v_cast_1201_){
_start:
{
lean_inc(v_cast_1201_);
return v_cast_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___boxed(lean_object* v_motive_1202_, lean_object* v_t_1203_, lean_object* v_h_1204_, lean_object* v_cast_1205_){
_start:
{
uint8_t v_t_boxed_1206_; lean_object* v_res_1207_; 
v_t_boxed_1206_ = lean_unbox(v_t_1203_);
v_res_1207_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(v_motive_1202_, v_t_boxed_1206_, v_h_1204_, v_cast_1205_);
lean_dec(v_cast_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(lean_object* v_no_1208_){
_start:
{
lean_inc(v_no_1208_);
return v_no_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg___boxed(lean_object* v_no_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(v_no_1209_);
lean_dec(v_no_1209_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(lean_object* v_motive_1211_, uint8_t v_t_1212_, lean_object* v_h_1213_, lean_object* v_no_1214_){
_start:
{
lean_inc(v_no_1214_);
return v_no_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___boxed(lean_object* v_motive_1215_, lean_object* v_t_1216_, lean_object* v_h_1217_, lean_object* v_no_1218_){
_start:
{
uint8_t v_t_boxed_1219_; lean_object* v_res_1220_; 
v_t_boxed_1219_ = lean_unbox(v_t_1216_);
v_res_1220_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(v_motive_1215_, v_t_boxed_1219_, v_h_1217_, v_no_1218_);
lean_dec(v_no_1218_);
return v_res_1220_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedResult_default(void){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = 0;
return v___x_1221_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult(void){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = 0;
return v___x_1222_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(lean_object* v_e_1263_){
_start:
{
lean_object* v_a_1269_; lean_object* v_b_1270_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
lean_inc_ref(v_e_1263_);
v___x_1274_ = l_Lean_Expr_cleanupAnnotations(v_e_1263_);
v___x_1275_ = l_Lean_Expr_isApp(v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v___x_1274_);
goto v___jp_1264_;
}
else
{
lean_object* v_arg_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_arg_1276_ = lean_ctor_get(v___x_1274_, 1);
lean_inc_ref(v_arg_1276_);
v___x_1277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1274_);
v___x_1278_ = l_Lean_Expr_isApp(v___x_1277_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1264_;
}
else
{
lean_object* v_arg_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_arg_1279_ = lean_ctor_get(v___x_1277_, 1);
lean_inc_ref(v_arg_1279_);
v___x_1280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1277_);
v___x_1281_ = l_Lean_Expr_isApp(v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1264_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1282_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1280_);
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2));
v___x_1284_ = l_Lean_Expr_isConstOf(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5));
v___x_1286_ = l_Lean_Expr_isConstOf(v___x_1282_, v___x_1285_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_Expr_isApp(v___x_1282_);
if (v___x_1287_ == 0)
{
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1264_;
}
else
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1282_);
v___x_1289_ = l_Lean_Expr_isApp(v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec_ref(v___x_1288_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1264_;
}
else
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1288_);
v___x_1291_ = l_Lean_Expr_isApp(v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1264_;
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1290_);
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8));
v___x_1294_ = l_Lean_Expr_isConstOf(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11));
v___x_1296_ = l_Lean_Expr_isConstOf(v___x_1292_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14));
v___x_1298_ = l_Lean_Expr_isConstOf(v___x_1292_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17));
v___x_1300_ = l_Lean_Expr_isConstOf(v___x_1292_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20));
v___x_1302_ = l_Lean_Expr_isConstOf(v___x_1292_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23));
v___x_1304_ = l_Lean_Expr_isConstOf(v___x_1292_, v___x_1303_);
lean_dec_ref(v___x_1292_);
if (v___x_1304_ == 0)
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1264_;
}
else
{
lean_dec_ref(v_e_1263_);
v_a_1269_ = v_arg_1279_;
v_b_1270_ = v_arg_1276_;
goto v___jp_1268_;
}
}
else
{
lean_dec_ref(v___x_1292_);
lean_dec_ref(v_e_1263_);
v_a_1269_ = v_arg_1279_;
v_b_1270_ = v_arg_1276_;
goto v___jp_1268_;
}
}
else
{
lean_dec_ref(v___x_1292_);
lean_dec_ref(v_e_1263_);
v_a_1269_ = v_arg_1279_;
v_b_1270_ = v_arg_1276_;
goto v___jp_1268_;
}
}
else
{
lean_dec_ref(v___x_1292_);
lean_dec_ref(v_e_1263_);
v_a_1269_ = v_arg_1279_;
v_b_1270_ = v_arg_1276_;
goto v___jp_1268_;
}
}
else
{
lean_dec_ref(v___x_1292_);
lean_dec_ref(v_e_1263_);
v_a_1269_ = v_arg_1279_;
v_b_1270_ = v_arg_1276_;
goto v___jp_1268_;
}
}
else
{
lean_dec_ref(v___x_1292_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_e_1263_);
v_e_1263_ = v_arg_1279_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_e_1263_);
v_e_1263_ = v_arg_1276_;
goto _start;
}
}
else
{
uint8_t v___x_1307_; 
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_e_1263_);
v___x_1307_ = 0;
return v___x_1307_;
}
}
}
}
v___jp_1264_:
{
uint8_t v___x_1265_; 
v___x_1265_ = l_Lean_Meta_Grind_isCastLikeApp(v_e_1263_);
lean_dec_ref(v_e_1263_);
if (v___x_1265_ == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = 2;
return v___x_1266_;
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = 1;
return v___x_1267_;
}
}
v___jp_1268_:
{
uint8_t v___x_1271_; 
v___x_1271_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_a_1269_);
switch(v___x_1271_)
{
case 0:
{
uint8_t v___x_1272_; 
v___x_1272_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_1270_);
if (v___x_1272_ == 0)
{
return v___x_1272_;
}
else
{
return v___x_1272_;
}
}
case 1:
{
uint8_t v___x_1273_; 
v___x_1273_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_1270_);
switch(v___x_1273_)
{
case 2:
{
return v___x_1273_;
}
case 1:
{
return v___x_1273_;
}
default: 
{
return v___x_1271_;
}
}
}
default: 
{
lean_dec_ref(v_b_1270_);
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___boxed(lean_object* v_e_1308_){
_start:
{
uint8_t v_res_1309_; lean_object* v_r_1310_; 
v_res_1309_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_1308_);
v_r_1310_ = lean_box(v_res_1309_);
return v_r_1310_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(lean_object* v_e_1311_){
_start:
{
uint8_t v___x_1312_; 
v___x_1312_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_1311_);
if (v___x_1312_ == 1)
{
uint8_t v___x_1313_; 
v___x_1313_ = 1;
return v___x_1313_;
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = 0;
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike___boxed(lean_object* v_e_1315_){
_start:
{
uint8_t v_res_1316_; lean_object* v_r_1317_; 
v_res_1316_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_1315_);
v_r_1317_ = lean_box(v_res_1316_);
return v_r_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(lean_object* v_declName_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; lean_object* v_env_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1321_ = lean_st_ref_get(v___y_1319_);
v_env_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_ref(v_env_1322_);
lean_dec(v___x_1321_);
v___x_1323_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1322_, v_declName_1318_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg___boxed(lean_object* v_declName_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1325_, v___y_1326_);
lean_dec(v___y_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(lean_object* v_declName_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1329_, v___y_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___boxed(lean_object* v_declName_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(v_declName_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp(lean_object* v_e_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
uint8_t v___x_1349_; uint8_t v___x_1350_; 
lean_inc_ref(v_e_1343_);
v___x_1349_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_1343_);
v___x_1350_ = 1;
if (v___x_1349_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Expr_getAppFn(v_e_1343_);
if (lean_obj_tag(v___x_1351_) == 4)
{
lean_object* v_declName_1352_; lean_object* v___y_1354_; lean_object* v___x_1369_; lean_object* v_a_1370_; 
v_declName_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_n(v_declName_1352_, 2);
lean_dec_ref_known(v___x_1351_, 2);
v___x_1369_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1352_, v_a_1347_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
if (lean_obj_tag(v_a_1370_) == 1)
{
lean_object* v_val_1371_; lean_object* v_numParams_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v_val_1371_ = lean_ctor_get(v_a_1370_, 0);
lean_inc(v_val_1371_);
lean_dec_ref_known(v_a_1370_, 1);
v_numParams_1372_ = lean_ctor_get(v_val_1371_, 1);
lean_inc(v_numParams_1372_);
lean_dec(v_val_1371_);
v___x_1373_ = l_Lean_Expr_getAppNumArgs(v_e_1343_);
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_add(v_numParams_1372_, v___x_1374_);
lean_dec(v_numParams_1372_);
v___x_1376_ = lean_nat_dec_eq(v___x_1373_, v___x_1375_);
lean_dec(v___x_1375_);
lean_dec(v___x_1373_);
if (v___x_1376_ == 0)
{
lean_dec_ref(v_e_1343_);
v___y_1354_ = v_a_1347_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = l_Lean_Expr_appArg_x21(v_e_1343_);
lean_dec_ref(v_e_1343_);
v___x_1378_ = l_Lean_Meta_isConstructorApp(v___x_1377_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1388_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1388_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1388_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_unbox(v_a_1379_);
lean_dec(v_a_1379_);
if (v___x_1383_ == 0)
{
lean_del_object(v___x_1381_);
v___y_1354_ = v_a_1347_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
lean_dec(v_declName_1352_);
v___x_1384_ = lean_box(v___x_1350_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1384_);
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_dec(v_declName_1352_);
return v___x_1378_;
}
}
}
else
{
lean_dec(v_a_1370_);
lean_dec_ref(v_e_1343_);
v___y_1354_ = v_a_1347_;
goto v___jp_1353_;
}
v___jp_1353_:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_st_ref_get(v___y_1354_);
v___x_1356_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_1352_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; 
v___x_1357_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(v_declName_1352_);
if (v___x_1357_ == 0)
{
uint8_t v___x_1358_; 
v___x_1358_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_1352_);
if (v___x_1358_ == 0)
{
lean_object* v_env_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_env_1359_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_ref(v_env_1359_);
lean_dec(v___x_1355_);
v___x_1360_ = l_Lean_Meta_isMatcherCore(v_env_1359_, v_declName_1352_);
v___x_1361_ = lean_box(v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v___x_1355_);
lean_dec(v_declName_1352_);
v___x_1363_ = lean_box(v___x_1350_);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v___x_1355_);
lean_dec(v_declName_1352_);
v___x_1365_ = lean_box(v___x_1350_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec(v___x_1355_);
lean_dec(v_declName_1352_);
v___x_1367_ = lean_box(v___x_1350_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
return v___x_1368_;
}
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v___x_1351_);
lean_dec_ref(v_e_1343_);
v___x_1389_ = lean_box(v___x_1349_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v_e_1343_);
v___x_1391_ = lean_box(v___x_1350_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp___boxed(lean_object* v_e_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Meta_Grind_isSupportApp(v_e_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
if (lean_obj_tag(v_a_1400_) == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = l_List_reverse___redArg(v_a_1401_);
return v___x_1402_;
}
else
{
lean_object* v_head_1403_; lean_object* v_tail_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1413_; 
v_head_1403_ = lean_ctor_get(v_a_1400_, 0);
v_tail_1404_ = lean_ctor_get(v_a_1400_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_a_1400_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1406_ = v_a_1400_;
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_tail_1404_);
lean_inc(v_head_1403_);
lean_dec(v_a_1400_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = l_Lean_MessageData_ofExpr(v_head_1403_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v_a_1401_);
lean_ctor_set(v___x_1406_, 0, v___x_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_a_1401_);
v___x_1410_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v_a_1400_ = v_tail_1404_;
v_a_1401_ = v___x_1410_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__2(void){
_start:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; double v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1417_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1418_ = 1;
v___x_1419_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1420_ = lean_box(0);
v___x_1421_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1422_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v___x_1420_);
lean_ctor_set(v___x_1422_, 2, v___x_1417_);
lean_ctor_set_float(v___x_1422_, sizeof(void*)*3, v___x_1419_);
lean_ctor_set_float(v___x_1422_, sizeof(void*)*3 + 8, v___x_1419_);
lean_ctor_set_uint8(v___x_1422_, sizeof(void*)*3 + 16, v___x_1418_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__5(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__4));
v___x_1427_ = l_Lean_MessageData_ofFormat(v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__6(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
v___x_1429_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__5, &l_Lean_Meta_Grind_ppEqc___closed__5_once, _init_l_Lean_Meta_Grind_ppEqc___closed__5);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppEqc(lean_object* v_eqc_1431_, lean_object* v_children_1432_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1433_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__2, &l_Lean_Meta_Grind_ppEqc___closed__2_once, _init_l_Lean_Meta_Grind_ppEqc___closed__2);
v___x_1434_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
v___x_1435_ = lean_box(0);
v___x_1436_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(v_eqc_1431_, v___x_1435_);
v___x_1437_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__6, &l_Lean_Meta_Grind_ppEqc___closed__6_once, _init_l_Lean_Meta_Grind_ppEqc___closed__6);
v___x_1438_ = l_Lean_MessageData_joinSep(v___x_1436_, v___x_1437_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1434_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1433_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
lean_ctor_set(v___x_1443_, 2, v_children_1432_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
if (lean_obj_tag(v_a_1444_) == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = l_List_reverse___redArg(v_a_1445_);
return v___x_1446_;
}
else
{
lean_object* v_head_1447_; lean_object* v_tail_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1458_; 
v_head_1447_ = lean_ctor_get(v_a_1444_, 0);
v_tail_1448_ = lean_ctor_get(v_a_1444_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_a_1444_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1450_ = v_a_1444_;
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_tail_1448_);
lean_inc(v_head_1447_);
lean_dec(v_a_1444_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint8_t v___x_1452_; 
lean_inc(v_head_1447_);
v___x_1452_ = l_Lean_Expr_isTrue(v_head_1447_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1454_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v_a_1445_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_head_1447_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_a_1445_);
v___x_1454_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
v_a_1444_ = v_tail_1448_;
v_a_1445_ = v___x_1454_;
goto _start;
}
}
else
{
lean_del_object(v___x_1450_);
lean_dec(v_head_1447_);
v_a_1444_ = v_tail_1448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
if (lean_obj_tag(v_a_1459_) == 0)
{
lean_object* v___x_1461_; 
v___x_1461_ = l_List_reverse___redArg(v_a_1460_);
return v___x_1461_;
}
else
{
lean_object* v_head_1462_; lean_object* v_tail_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1473_; 
v_head_1462_ = lean_ctor_get(v_a_1459_, 0);
v_tail_1463_ = lean_ctor_get(v_a_1459_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_a_1459_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1465_ = v_a_1459_;
v_isShared_1466_ = v_isSharedCheck_1473_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_tail_1463_);
lean_inc(v_head_1462_);
lean_dec(v_a_1459_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1473_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
uint8_t v___x_1467_; 
lean_inc(v_head_1462_);
v___x_1467_ = l_Lean_Expr_isFalse(v_head_1462_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1469_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v_a_1460_);
v___x_1469_ = v___x_1465_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_head_1462_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_a_1460_);
v___x_1469_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
v_a_1459_ = v_tail_1463_;
v_a_1460_ = v___x_1469_;
goto _start;
}
}
else
{
lean_del_object(v___x_1465_);
lean_dec(v_head_1462_);
v_a_1459_ = v_tail_1463_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(lean_object* v_x_1474_){
_start:
{
if (lean_obj_tag(v_x_1474_) == 0)
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_box(0);
return v___x_1475_;
}
else
{
lean_object* v_head_1476_; lean_object* v_tail_1477_; uint8_t v___x_1478_; 
v_head_1476_ = lean_ctor_get(v_x_1474_, 0);
lean_inc_n(v_head_1476_, 2);
v_tail_1477_ = lean_ctor_get(v_x_1474_, 1);
lean_inc(v_tail_1477_);
lean_dec_ref_known(v_x_1474_, 2);
v___x_1478_ = l_Lean_Expr_isTrue(v_head_1476_);
if (v___x_1478_ == 0)
{
lean_dec(v_head_1476_);
v_x_1474_ = v_tail_1477_;
goto _start;
}
else
{
lean_object* v___x_1480_; 
lean_dec(v_tail_1477_);
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_head_1476_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(lean_object* v_x_1481_, lean_object* v_x_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_x_1482_);
lean_ctor_set(v___x_1489_, 1, v___y_1483_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
else
{
lean_object* v_head_1491_; lean_object* v_tail_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1512_; 
v_head_1491_ = lean_ctor_get(v_x_1481_, 0);
v_tail_1492_ = lean_ctor_get(v_x_1481_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_x_1481_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1494_ = v_x_1481_;
v_isShared_1495_ = v_isSharedCheck_1512_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_tail_1492_);
lean_inc(v_head_1491_);
lean_dec(v_x_1481_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1512_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; 
lean_inc(v_head_1491_);
v___x_1496_ = l_Lean_Meta_Grind_isSupportApp(v_head_1491_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; uint8_t v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = lean_unbox(v_a_1497_);
lean_dec(v_a_1497_);
if (v___x_1498_ == 0)
{
lean_del_object(v___x_1494_);
lean_dec(v_head_1491_);
v_x_1481_ = v_tail_1492_;
goto _start;
}
else
{
lean_object* v___x_1501_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v_x_1482_);
v___x_1501_ = v___x_1494_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_head_1491_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_x_1482_);
v___x_1501_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
v_x_1481_ = v_tail_1492_;
v_x_1482_ = v___x_1501_;
goto _start;
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_del_object(v___x_1494_);
lean_dec(v_tail_1492_);
lean_dec(v_head_1491_);
lean_dec_ref(v___y_1483_);
lean_dec(v_x_1482_);
v_a_1504_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1496_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1496_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg___boxed(lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_x_1513_, v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1522_) == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_box(0);
return v___x_1523_;
}
else
{
lean_object* v_head_1524_; lean_object* v_tail_1525_; uint8_t v___x_1526_; 
v_head_1524_ = lean_ctor_get(v_x_1522_, 0);
lean_inc_n(v_head_1524_, 2);
v_tail_1525_ = lean_ctor_get(v_x_1522_, 1);
lean_inc(v_tail_1525_);
lean_dec_ref_known(v_x_1522_, 2);
v___x_1526_ = l_Lean_Expr_isFalse(v_head_1524_);
if (v___x_1526_ == 0)
{
lean_dec(v_head_1524_);
v_x_1522_ = v_tail_1525_;
goto _start;
}
else
{
lean_object* v___x_1528_; 
lean_dec(v_tail_1525_);
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_head_1524_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(uint8_t v_a_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
if (lean_obj_tag(v_x_1530_) == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_x_1531_);
lean_ctor_set(v___x_1538_, 1, v___y_1532_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
else
{
lean_object* v_head_1540_; lean_object* v_tail_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1563_; 
v_head_1540_ = lean_ctor_get(v_x_1530_, 0);
v_tail_1541_ = lean_ctor_get(v_x_1530_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_x_1530_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1543_ = v_x_1530_;
v_isShared_1544_ = v_isSharedCheck_1563_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_tail_1541_);
lean_inc(v_head_1540_);
lean_dec(v_x_1530_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1563_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; 
lean_inc(v_head_1540_);
v___x_1545_ = l_Lean_Meta_Grind_isSupportApp(v_head_1540_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v_snd_1548_; uint8_t v___x_1553_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1553_ = lean_unbox(v_a_1546_);
lean_dec(v_a_1546_);
if (v___x_1553_ == 0)
{
v_snd_1548_ = v___y_1532_;
goto v___jp_1547_;
}
else
{
if (v_a_1529_ == 0)
{
lean_del_object(v___x_1543_);
lean_dec(v_head_1540_);
v_x_1530_ = v_tail_1541_;
goto _start;
}
else
{
v_snd_1548_ = v___y_1532_;
goto v___jp_1547_;
}
}
v___jp_1547_:
{
lean_object* v___x_1550_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v_x_1531_);
v___x_1550_ = v___x_1543_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_head_1540_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_x_1531_);
v___x_1550_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
v_x_1530_ = v_tail_1541_;
v_x_1531_ = v___x_1550_;
v___y_1532_ = v_snd_1548_;
goto _start;
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_del_object(v___x_1543_);
lean_dec(v_tail_1541_);
lean_dec(v_head_1540_);
lean_dec_ref(v___y_1532_);
lean_dec(v_x_1531_);
v_a_1555_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1545_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1545_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg___boxed(lean_object* v_a_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v_a_20243__boxed_1573_; lean_object* v_res_1574_; 
v_a_20243__boxed_1573_ = lean_unbox(v_a_1564_);
v_res_1574_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_a_20243__boxed_1573_, v_x_1565_, v_x_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(uint8_t v_collapsedProps_1580_, lean_object* v_as_x27_1581_, lean_object* v_b_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
if (lean_obj_tag(v_as_x27_1581_) == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_b_1582_);
lean_ctor_set(v___x_1590_, 1, v___y_1584_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
else
{
lean_object* v_snd_1592_; lean_object* v_snd_1593_; lean_object* v_head_1594_; lean_object* v_tail_1595_; lean_object* v_fst_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1760_; 
v_snd_1592_ = lean_ctor_get(v_b_1582_, 1);
lean_inc(v_snd_1592_);
v_snd_1593_ = lean_ctor_get(v_snd_1592_, 1);
lean_inc(v_snd_1593_);
v_head_1594_ = lean_ctor_get(v_as_x27_1581_, 0);
v_tail_1595_ = lean_ctor_get(v_as_x27_1581_, 1);
v_fst_1596_ = lean_ctor_get(v_b_1582_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_b_1582_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v_b_1582_, 1);
lean_dec(v_unused_1761_);
v___x_1598_ = v_b_1582_;
v_isShared_1599_ = v_isSharedCheck_1760_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_fst_1596_);
lean_dec(v_b_1582_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1760_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_fst_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1758_; 
v_fst_1600_ = lean_ctor_get(v_snd_1592_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_snd_1592_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; 
v_unused_1759_ = lean_ctor_get(v_snd_1592_, 1);
lean_dec(v_unused_1759_);
v___x_1602_ = v_snd_1592_;
v_isShared_1603_ = v_isSharedCheck_1758_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_fst_1600_);
lean_dec(v_snd_1592_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1758_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_fst_1604_; lean_object* v_snd_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1757_; 
v_fst_1604_ = lean_ctor_get(v_snd_1593_, 0);
v_snd_1605_ = lean_ctor_get(v_snd_1593_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_snd_1593_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1607_ = v_snd_1593_;
v_isShared_1608_ = v_isSharedCheck_1757_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_snd_1605_);
lean_inc(v_fst_1604_);
lean_dec(v_snd_1593_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1757_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___y_1610_; lean_object* v___x_1621_; 
lean_inc(v_head_1594_);
v___x_1621_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(v_head_1594_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; 
lean_inc(v_head_1594_);
v___x_1622_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(v_head_1594_);
if (lean_obj_tag(v___x_1622_) == 0)
{
if (lean_obj_tag(v_head_1594_) == 1)
{
lean_object* v_tail_1623_; 
v_tail_1623_ = lean_ctor_get(v_head_1594_, 1);
if (lean_obj_tag(v_tail_1623_) == 1)
{
lean_object* v_head_1624_; lean_object* v___x_1625_; 
lean_del_object(v___x_1607_);
lean_del_object(v___x_1602_);
lean_del_object(v___x_1598_);
v_head_1624_ = lean_ctor_get(v_head_1594_, 0);
lean_inc(v_head_1624_);
v___x_1625_ = l_Lean_Meta_isProof(v_head_1624_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; uint8_t v___x_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = lean_unbox(v_a_1626_);
if (v___x_1627_ == 0)
{
lean_object* v_regularEqcs_1628_; lean_object* v___y_1630_; lean_object* v_fst_1631_; lean_object* v_snd_1632_; lean_object* v_fst_1651_; lean_object* v_snd_1652_; lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; 
v_regularEqcs_1628_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_unbox(v_a_1626_);
lean_dec(v_a_1626_);
lean_inc_ref(v_head_1594_);
v___x_1681_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v___x_1680_, v_head_1594_, v___x_1679_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v_fst_1683_; lean_object* v_snd_1684_; lean_object* v___x_1685_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v_fst_1683_ = lean_ctor_get(v_a_1682_, 0);
lean_inc(v_fst_1683_);
v_snd_1684_ = lean_ctor_get(v_a_1682_, 1);
lean_inc(v_snd_1684_);
lean_dec(v_a_1682_);
v___x_1685_ = l_List_reverse___redArg(v_fst_1683_);
v_fst_1651_ = v___x_1685_;
v_snd_1652_ = v_snd_1684_;
goto v___jp_1650_;
}
else
{
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1686_; lean_object* v_fst_1687_; lean_object* v_snd_1688_; 
v_a_1686_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1681_, 1);
v_fst_1687_ = lean_ctor_get(v_a_1686_, 0);
lean_inc(v_fst_1687_);
v_snd_1688_ = lean_ctor_get(v_a_1686_, 1);
lean_inc(v_snd_1688_);
lean_dec(v_a_1686_);
v_fst_1651_ = v_fst_1687_;
v_snd_1652_ = v_snd_1688_;
goto v___jp_1650_;
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_snd_1605_);
lean_dec(v_fst_1604_);
lean_dec(v_fst_1600_);
lean_dec(v_fst_1596_);
v_a_1689_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1681_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1681_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
v___jp_1629_:
{
uint8_t v___x_1633_; 
v___x_1633_ = l_List_isEmpty___redArg(v_fst_1631_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1634_ = l_Lean_Meta_Grind_ppEqc(v_fst_1631_, v_regularEqcs_1628_);
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_mk_empty_array_with_capacity(v___x_1635_);
v___x_1637_ = lean_array_push(v___x_1636_, v___x_1634_);
v___x_1638_ = l_Lean_Meta_Grind_ppEqc(v___y_1630_, v___x_1637_);
v___x_1639_ = lean_array_push(v_fst_1604_, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_snd_1605_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_fst_1600_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_fst_1596_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1642_;
v___y_1584_ = v_snd_1632_;
goto _start;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v_fst_1631_);
v___x_1644_ = l_Lean_Meta_Grind_ppEqc(v___y_1630_, v_regularEqcs_1628_);
v___x_1645_ = lean_array_push(v_fst_1604_, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v_snd_1605_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_fst_1600_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_fst_1596_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1648_;
v___y_1584_ = v_snd_1632_;
goto _start;
}
}
v___jp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = l_List_lengthTR___redArg(v_fst_1651_);
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_dec_le(v___x_1653_, v___x_1654_);
lean_dec(v___x_1653_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_box(0);
lean_inc_ref(v_head_1594_);
v___x_1657_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_head_1594_, v___x_1656_, v_snd_1652_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v_fst_1659_; lean_object* v_snd_1660_; lean_object* v___x_1661_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v_fst_1659_ = lean_ctor_get(v_a_1658_, 0);
lean_inc(v_fst_1659_);
v_snd_1660_ = lean_ctor_get(v_a_1658_, 1);
lean_inc(v_snd_1660_);
lean_dec(v_a_1658_);
v___x_1661_ = l_List_reverse___redArg(v_fst_1659_);
v___y_1630_ = v_fst_1651_;
v_fst_1631_ = v___x_1661_;
v_snd_1632_ = v_snd_1660_;
goto v___jp_1629_;
}
else
{
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1662_; lean_object* v_fst_1663_; lean_object* v_snd_1664_; 
v_a_1662_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1657_, 1);
v_fst_1663_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_fst_1663_);
v_snd_1664_ = lean_ctor_get(v_a_1662_, 1);
lean_inc(v_snd_1664_);
lean_dec(v_a_1662_);
v___y_1630_ = v_fst_1651_;
v_fst_1631_ = v_fst_1663_;
v_snd_1632_ = v_snd_1664_;
goto v___jp_1629_;
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_fst_1651_);
lean_dec(v_snd_1605_);
lean_dec(v_fst_1604_);
lean_dec(v_fst_1600_);
lean_dec(v_fst_1596_);
v_a_1665_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1657_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1657_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v_fst_1651_);
lean_inc_ref(v_head_1594_);
v___x_1673_ = l_Lean_Meta_Grind_ppEqc(v_head_1594_, v_regularEqcs_1628_);
v___x_1674_ = lean_array_push(v_snd_1605_, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_fst_1604_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_fst_1600_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_fst_1596_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1677_;
v___y_1584_ = v_snd_1652_;
goto _start;
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec(v_a_1626_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_fst_1604_);
lean_ctor_set(v___x_1697_, 1, v_snd_1605_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_fst_1600_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_fst_1596_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1699_;
goto _start;
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_snd_1605_);
lean_dec(v_fst_1604_);
lean_dec(v_fst_1600_);
lean_dec(v_fst_1596_);
lean_dec_ref(v___y_1584_);
v_a_1701_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1625_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1625_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
v___y_1610_ = v___y_1584_;
goto v___jp_1609_;
}
}
else
{
v___y_1610_ = v___y_1584_;
goto v___jp_1609_;
}
}
else
{
lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1731_; 
lean_del_object(v___x_1607_);
lean_del_object(v___x_1602_);
lean_del_object(v___x_1598_);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v___x_1622_, 0);
lean_dec(v_unused_1732_);
v___x_1710_ = v___x_1622_;
v_isShared_1711_ = v_isSharedCheck_1731_;
goto v_resetjp_1709_;
}
else
{
lean_dec(v___x_1622_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1731_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1712_ = lean_box(0);
lean_inc(v_head_1594_);
v___x_1713_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(v_head_1594_, v___x_1712_);
v___x_1714_ = l_List_isEmpty___redArg(v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
lean_dec(v_fst_1600_);
v___x_1715_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1716_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0));
v___x_1717_ = lean_array_mk(v___x_1713_);
v___x_1718_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_1719_ = l_Lean_Meta_Grind_ppExprArray(v___x_1715_, v___x_1716_, v___x_1717_, v___x_1718_, v_collapsedProps_1580_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1719_);
v___x_1721_ = v___x_1710_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_fst_1604_);
lean_ctor_set(v___x_1722_, 1, v_snd_1605_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_fst_1596_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1724_;
goto _start;
}
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v___x_1713_);
lean_del_object(v___x_1710_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v_fst_1604_);
lean_ctor_set(v___x_1727_, 1, v_snd_1605_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_fst_1600_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_fst_1596_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1729_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1755_; 
lean_del_object(v___x_1607_);
lean_del_object(v___x_1602_);
lean_del_object(v___x_1598_);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1756_);
v___x_1734_ = v___x_1621_;
v_isShared_1735_ = v_isSharedCheck_1755_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v___x_1621_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1755_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = lean_box(0);
lean_inc(v_head_1594_);
v___x_1737_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(v_head_1594_, v___x_1736_);
v___x_1738_ = l_List_isEmpty___redArg(v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
lean_dec(v_fst_1596_);
v___x_1739_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1740_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3));
v___x_1741_ = lean_array_mk(v___x_1737_);
v___x_1742_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_1743_ = l_Lean_Meta_Grind_ppExprArray(v___x_1739_, v___x_1740_, v___x_1741_, v___x_1742_, v_collapsedProps_1580_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1743_);
v___x_1745_ = v___x_1734_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_fst_1604_);
lean_ctor_set(v___x_1746_, 1, v_snd_1605_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_fst_1600_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1745_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1748_;
goto _start;
}
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec(v___x_1737_);
lean_del_object(v___x_1734_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_fst_1604_);
lean_ctor_set(v___x_1751_, 1, v_snd_1605_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_fst_1600_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_fst_1596_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1753_;
goto _start;
}
}
}
v___jp_1609_:
{
lean_object* v___x_1612_; 
if (v_isShared_1608_ == 0)
{
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_fst_1604_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_snd_1605_);
v___x_1612_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1614_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v___x_1612_);
v___x_1614_ = v___x_1602_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_fst_1600_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1614_);
v___x_1616_ = v___x_1598_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_fst_1596_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
v_as_x27_1581_ = v_tail_1595_;
v_b_1582_ = v___x_1616_;
v___y_1584_ = v___y_1610_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___boxed(lean_object* v_collapsedProps_1762_, lean_object* v_as_x27_1763_, lean_object* v_b_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
uint8_t v_collapsedProps_boxed_1772_; lean_object* v_res_1773_; 
v_collapsedProps_boxed_1772_ = lean_unbox(v_collapsedProps_1762_);
v_res_1773_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_boxed_1772_, v_as_x27_1763_, v_b_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1765_);
lean_dec(v_as_x27_1763_);
return v_res_1773_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0(void){
_start:
{
lean_object* v___x_1774_; uint8_t v___x_1775_; double v___x_1776_; lean_object* v_trueEqc_x3f_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1774_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1775_ = 1;
v___x_1776_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v_trueEqc_x3f_1777_ = lean_box(0);
v___x_1778_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1779_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_trueEqc_x3f_1777_);
lean_ctor_set(v___x_1779_, 2, v___x_1774_);
lean_ctor_set_float(v___x_1779_, sizeof(void*)*3, v___x_1776_);
lean_ctor_set_float(v___x_1779_, sizeof(void*)*3 + 8, v___x_1776_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*3 + 16, v___x_1775_);
return v___x_1779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2));
v___x_1784_ = l_Lean_MessageData_ofFormat(v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8));
v___x_1797_ = l_Lean_MessageData_ofFormat(v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(uint8_t v_collapsedProps_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = 1;
v___x_1820_ = l_Lean_Meta_Grind_Goal_getEqcs(v_a_1799_, v___x_1807_);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6));
v___x_1822_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_1798_, v___x_1820_, v___x_1821_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v___x_1820_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v_fst_1824_; lean_object* v_snd_1825_; lean_object* v_snd_1826_; lean_object* v_fst_1827_; lean_object* v_fst_1828_; lean_object* v_snd_1829_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v_regularEqcs_1838_; lean_object* v___y_1839_; lean_object* v_fst_1844_; lean_object* v_snd_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v_fst_1824_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_fst_1824_);
v_snd_1825_ = lean_ctor_get(v_fst_1824_, 1);
lean_inc(v_snd_1825_);
v_snd_1826_ = lean_ctor_get(v_a_1823_, 1);
lean_inc(v_snd_1826_);
lean_dec(v_a_1823_);
v_fst_1827_ = lean_ctor_get(v_fst_1824_, 0);
lean_inc(v_fst_1827_);
lean_dec(v_fst_1824_);
v_fst_1828_ = lean_ctor_get(v_snd_1825_, 0);
lean_inc(v_fst_1828_);
v_snd_1829_ = lean_ctor_get(v_snd_1825_, 1);
lean_inc(v_snd_1829_);
lean_dec(v_snd_1825_);
v_fst_1844_ = lean_ctor_get(v_snd_1829_, 0);
lean_inc(v_fst_1844_);
v_snd_1845_ = lean_ctor_get(v_snd_1829_, 1);
lean_inc(v_snd_1845_);
lean_dec(v_snd_1829_);
v___x_1846_ = lean_array_get_size(v_snd_1845_);
v___x_1847_ = lean_nat_dec_eq(v___x_1846_, v___x_1806_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
v___x_1849_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9);
v___x_1850_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
lean_ctor_set(v___x_1850_, 2, v_snd_1845_);
v___x_1851_ = lean_array_push(v_fst_1844_, v___x_1850_);
v_regularEqcs_1838_ = v___x_1851_;
v___y_1839_ = v_snd_1826_;
goto v___jp_1837_;
}
else
{
lean_dec(v_snd_1845_);
v_regularEqcs_1838_ = v_fst_1844_;
v___y_1839_ = v_snd_1826_;
goto v___jp_1837_;
}
v___jp_1830_:
{
if (lean_obj_tag(v_fst_1828_) == 1)
{
lean_object* v_val_1833_; lean_object* v___x_1834_; lean_object* v_a_1835_; lean_object* v_snd_1836_; 
v_val_1833_ = lean_ctor_get(v_fst_1828_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v_fst_1828_, 1);
v___x_1834_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_1833_, v___y_1832_);
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v___x_1834_);
v_snd_1836_ = lean_ctor_get(v_a_1835_, 1);
lean_inc(v_snd_1836_);
lean_dec(v_a_1835_);
v___y_1809_ = v___y_1831_;
v___y_1810_ = v_snd_1836_;
goto v___jp_1808_;
}
else
{
lean_dec(v_fst_1828_);
v___y_1809_ = v___y_1831_;
v___y_1810_ = v___y_1832_;
goto v___jp_1808_;
}
}
v___jp_1837_:
{
if (lean_obj_tag(v_fst_1827_) == 1)
{
lean_object* v_val_1840_; lean_object* v___x_1841_; lean_object* v_a_1842_; lean_object* v_snd_1843_; 
v_val_1840_ = lean_ctor_get(v_fst_1827_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v_fst_1827_, 1);
v___x_1841_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_1840_, v___y_1839_);
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v_snd_1843_ = lean_ctor_get(v_a_1842_, 1);
lean_inc(v_snd_1843_);
lean_dec(v_a_1842_);
v___y_1831_ = v_regularEqcs_1838_;
v___y_1832_ = v_snd_1843_;
goto v___jp_1830_;
}
else
{
lean_dec(v_fst_1827_);
v___y_1831_ = v_regularEqcs_1838_;
v___y_1832_ = v___y_1839_;
goto v___jp_1830_;
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_a_1852_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1822_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1822_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
v___jp_1808_:
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = lean_array_get_size(v___y_1809_);
v___x_1812_ = lean_nat_dec_eq(v___x_1811_, v___x_1806_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
v___x_1814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3);
v___x_1815_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
lean_ctor_set(v___x_1815_, 2, v___y_1809_);
v___x_1816_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_1815_, v___y_1810_);
return v___x_1816_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec_ref(v___y_1809_);
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v___y_1810_);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___boxed(lean_object* v_collapsedProps_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
uint8_t v_collapsedProps_boxed_1868_; lean_object* v_res_1869_; 
v_collapsedProps_boxed_1868_ = lean_unbox(v_collapsedProps_1860_);
v_res_1869_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(v_collapsedProps_boxed_1868_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec_ref(v_a_1861_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_x_1870_, v_x_1871_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___boxed(lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(v_x_1880_, v_x_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec_ref(v___y_1882_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(uint8_t v_a_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_a_1890_, v_x_1891_, v_x_1892_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___boxed(lean_object* v_a_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v_a_20916__boxed_1911_; lean_object* v_res_1912_; 
v_a_20916__boxed_1911_ = lean_unbox(v_a_1901_);
v_res_1912_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(v_a_20916__boxed_1911_, v_x_1902_, v_x_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v___y_1904_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(uint8_t v_collapsedProps_1913_, lean_object* v_as_1914_, lean_object* v_as_x27_1915_, lean_object* v_b_1916_, lean_object* v_a_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_1913_, v_as_x27_1915_, v_b_1916_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___boxed(lean_object* v_collapsedProps_1926_, lean_object* v_as_1927_, lean_object* v_as_x27_1928_, lean_object* v_b_1929_, lean_object* v_a_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
uint8_t v_collapsedProps_boxed_1938_; lean_object* v_res_1939_; 
v_collapsedProps_boxed_1938_ = lean_unbox(v_collapsedProps_1926_);
v_res_1939_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(v_collapsedProps_boxed_1938_, v_as_1927_, v_as_x27_1928_, v_b_1929_, v_a_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec_ref(v___y_1931_);
lean_dec(v_as_x27_1928_);
lean_dec(v_as_1927_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
if (lean_obj_tag(v_a_1940_) == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = l_List_reverse___redArg(v_a_1941_);
return v___x_1942_;
}
else
{
lean_object* v_head_1943_; lean_object* v_tail_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1953_; 
v_head_1943_ = lean_ctor_get(v_a_1940_, 0);
v_tail_1944_ = lean_ctor_get(v_a_1940_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_a_1940_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1946_ = v_a_1940_;
v_isShared_1947_ = v_isSharedCheck_1953_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_tail_1944_);
lean_inc(v_head_1943_);
lean_dec(v_a_1940_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1953_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = l_Lean_Meta_Grind_ppPattern(v_head_1943_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 1, v_a_1941_);
lean_ctor_set(v___x_1946_, 0, v___x_1948_);
v___x_1950_ = v___x_1946_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_a_1941_);
v___x_1950_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
v_a_1940_ = v_tail_1944_;
v_a_1941_ = v___x_1950_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
if (lean_obj_tag(v_a_1954_) == 0)
{
lean_object* v___x_1956_; 
v___x_1956_ = l_List_reverse___redArg(v_a_1955_);
return v___x_1956_;
}
else
{
lean_object* v_head_1957_; lean_object* v_tail_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1966_; 
v_head_1957_ = lean_ctor_get(v_a_1954_, 0);
v_tail_1958_ = lean_ctor_get(v_a_1954_, 1);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_a_1954_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1960_ = v_a_1954_;
v_isShared_1961_ = v_isSharedCheck_1966_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_tail_1958_);
lean_inc(v_head_1957_);
lean_dec(v_a_1954_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1966_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v_a_1955_);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_head_1957_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_a_1955_);
v___x_1963_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
v_a_1954_ = v_tail_1958_;
v_a_1955_ = v___x_1963_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4(void){
_start:
{
lean_object* v___x_1973_; uint8_t v___x_1974_; double v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1973_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1974_ = 1;
v___x_1975_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1976_ = lean_box(0);
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3));
v___x_1978_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v___x_1976_);
lean_ctor_set(v___x_1978_, 2, v___x_1973_);
lean_ctor_set_float(v___x_1978_, sizeof(void*)*3, v___x_1975_);
lean_ctor_set_float(v___x_1978_, sizeof(void*)*3 + 8, v___x_1975_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*3 + 16, v___x_1974_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(lean_object* v_thm_1979_){
_start:
{
lean_object* v_patterns_1981_; lean_object* v_origin_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v_m_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_patterns_1981_ = lean_ctor_get(v_thm_1979_, 3);
lean_inc(v_patterns_1981_);
v_origin_1982_ = lean_ctor_get(v_thm_1979_, 5);
lean_inc_ref(v_origin_1982_);
lean_dec_ref(v_thm_1979_);
v___x_1983_ = l_Lean_Meta_Grind_Origin_pp(v_origin_1982_);
v___x_1984_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_box(0);
v___x_1987_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(v_patterns_1981_, v___x_1986_);
v___x_1988_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(v___x_1987_, v___x_1986_);
v___x_1989_ = l_Lean_MessageData_ofList(v___x_1988_);
v_m_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_1990_, 0, v___x_1985_);
lean_ctor_set(v_m_1990_, 1, v___x_1989_);
v___x_1991_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4);
v___x_1992_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1993_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v_m_1990_);
lean_ctor_set(v___x_1993_, 2, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___boxed(lean_object* v_thm_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_thm_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(lean_object* v_thm_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_thm_1998_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___boxed(lean_object* v_thm_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(v_thm_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(size_t v_sz_2012_, size_t v_i_2013_, lean_object* v_bs_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_usize_dec_lt(v_i_2013_, v_sz_2012_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_bs_2014_);
lean_ctor_set(v___x_2018_, 1, v___y_2015_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
else
{
lean_object* v_v_2020_; lean_object* v___x_2021_; 
v_v_2020_ = lean_array_uget_borrowed(v_bs_2014_, v_i_2013_);
lean_inc(v_v_2020_);
v___x_2021_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_v_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v_bs_x27_2024_; size_t v___x_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = lean_unsigned_to_nat(0u);
v_bs_x27_2024_ = lean_array_uset(v_bs_2014_, v_i_2013_, v___x_2023_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2013_, v___x_2025_);
v___x_2027_ = lean_array_uset(v_bs_x27_2024_, v_i_2013_, v_a_2022_);
v_i_2013_ = v___x_2026_;
v_bs_2014_ = v___x_2027_;
goto _start;
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec_ref(v___y_2015_);
lean_dec_ref(v_bs_2014_);
v_a_2029_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2021_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2021_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg___boxed(lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_bs_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_boxed_2042_, v_i_boxed_2043_, v_bs_2039_, v___y_2040_);
return v_res_2044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2(void){
_start:
{
lean_object* v___x_2048_; uint8_t v___x_2049_; double v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2048_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2049_ = 1;
v___x_2050_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2051_ = lean_box(0);
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1));
v___x_2053_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v___x_2051_);
lean_ctor_set(v___x_2053_, 2, v___x_2048_);
lean_ctor_set_float(v___x_2053_, sizeof(void*)*3, v___x_2050_);
lean_ctor_set_float(v___x_2053_, sizeof(void*)*3 + 8, v___x_2050_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*3 + 16, v___x_2049_);
return v___x_2053_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4));
v___x_2058_ = l_Lean_MessageData_ofFormat(v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_toGoalState_2066_; lean_object* v_ematch_2067_; lean_object* v_thms_2068_; lean_object* v_newThms_2069_; lean_object* v___x_2070_; size_t v_sz_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v_toGoalState_2066_ = lean_ctor_get(v_a_2059_, 0);
v_ematch_2067_ = lean_ctor_get(v_toGoalState_2066_, 12);
v_thms_2068_ = lean_ctor_get(v_ematch_2067_, 2);
v_newThms_2069_ = lean_ctor_get(v_ematch_2067_, 3);
v___x_2070_ = l_Lean_PersistentArray_toArray___redArg(v_thms_2068_);
v_sz_2071_ = lean_array_size(v___x_2070_);
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2071_, v___x_2072_, v___x_2070_, v_a_2060_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2077_; size_t v_sz_2078_; lean_object* v___x_2079_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v_fst_2075_ = lean_ctor_get(v_a_2074_, 0);
lean_inc(v_fst_2075_);
v_snd_2076_ = lean_ctor_get(v_a_2074_, 1);
lean_inc(v_snd_2076_);
lean_dec(v_a_2074_);
v___x_2077_ = l_Lean_PersistentArray_toArray___redArg(v_newThms_2069_);
v_sz_2078_ = lean_array_size(v___x_2077_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2078_, v___x_2072_, v___x_2077_, v_snd_2076_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2105_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2105_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2105_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_fst_2084_; lean_object* v_snd_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2104_; 
v_fst_2084_ = lean_ctor_get(v_a_2080_, 0);
v_snd_2085_ = lean_ctor_get(v_a_2080_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2087_ = v_a_2080_;
v_isShared_2088_ = v_isSharedCheck_2104_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_snd_2085_);
lean_inc(v_fst_2084_);
lean_dec(v_a_2080_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2104_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2089_ = l_Array_append___redArg(v_fst_2075_, v_fst_2084_);
lean_dec(v_fst_2084_);
v___x_2090_ = lean_array_get_size(v___x_2089_);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_nat_dec_eq(v___x_2090_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_del_object(v___x_2087_);
lean_del_object(v___x_2082_);
v___x_2093_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2);
v___x_2094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5);
v___x_2095_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2093_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
lean_ctor_set(v___x_2095_, 2, v___x_2089_);
v___x_2096_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2095_, v_snd_2085_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
lean_dec_ref(v___x_2089_);
v___x_2097_ = lean_box(0);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2097_);
v___x_2099_ = v___x_2087_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_snd_2085_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2099_);
v___x_2101_ = v___x_2082_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_fst_2075_);
v_a_2106_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2079_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2079_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2073_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2073_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___boxed(lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec_ref(v_a_2122_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(size_t v_sz_2130_, size_t v_i_2131_, lean_object* v_bs_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2130_, v_i_2131_, v_bs_2132_, v___y_2134_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___boxed(lean_object* v_sz_2141_, lean_object* v_i_2142_, lean_object* v_bs_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
size_t v_sz_boxed_2151_; size_t v_i_boxed_2152_; lean_object* v_res_2153_; 
v_sz_boxed_2151_ = lean_unbox_usize(v_sz_2141_);
lean_dec(v_sz_2141_);
v_i_boxed_2152_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_res_2153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(v_sz_boxed_2151_, v_i_boxed_2152_, v_bs_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec_ref(v___y_2144_);
return v_res_2153_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(lean_object* v_x_2154_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg___boxed(lean_object* v_x_2156_){
_start:
{
uint8_t v_res_2157_; lean_object* v_r_2158_; 
v_res_2157_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(v_x_2156_);
lean_dec_ref(v_x_2156_);
v_r_2158_ = lean_box(v_res_2157_);
return v_r_2158_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(lean_object* v_00_u03b2_2159_, lean_object* v_x_2160_){
_start:
{
uint8_t v___x_2161_; 
v___x_2161_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___boxed(lean_object* v_00_u03b2_2162_, lean_object* v_x_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(v_00_u03b2_2162_, v_x_2163_);
lean_dec_ref(v_x_2163_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(lean_object* v_as_2170_, size_t v_sz_2171_, size_t v_i_2172_, lean_object* v_b_2173_){
_start:
{
uint8_t v___x_2175_; 
v___x_2175_ = lean_usize_dec_lt(v_i_2172_, v_sz_2171_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_b_2173_);
return v___x_2176_;
}
else
{
lean_object* v_a_2177_; lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2220_; 
v_a_2177_ = lean_array_uget(v_as_2170_, v_i_2172_);
v_fst_2178_ = lean_ctor_get(v_a_2177_, 0);
v_snd_2179_ = lean_ctor_get(v_a_2177_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_a_2177_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2181_ = v_a_2177_;
v_isShared_2182_ = v_isSharedCheck_2220_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_inc(v_fst_2178_);
lean_dec(v_a_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2220_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; double v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v_num_2189_; lean_object* v_den_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2219_; 
v___x_2183_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1));
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2187_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2188_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2188_, 0, v___x_2184_);
lean_ctor_set(v___x_2188_, 1, v___x_2185_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
lean_ctor_set_float(v___x_2188_, sizeof(void*)*3, v___x_2186_);
lean_ctor_set_float(v___x_2188_, sizeof(void*)*3 + 8, v___x_2186_);
lean_ctor_set_uint8(v___x_2188_, sizeof(void*)*3 + 16, v___x_2175_);
v_num_2189_ = lean_ctor_get(v_snd_2179_, 0);
v_den_2190_ = lean_ctor_get(v_snd_2179_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_snd_2179_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2192_ = v_snd_2179_;
v_isShared_2193_ = v_isSharedCheck_2219_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_den_2190_);
lean_inc(v_num_2189_);
lean_dec(v_snd_2179_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2219_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2194_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2178_);
v___x_2195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 7);
lean_ctor_set(v___x_2192_, 1, v___x_2195_);
lean_ctor_set(v___x_2192_, 0, v___x_2194_);
v___x_2197_ = v___x_2192_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___y_2199_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_dec_eq(v_den_2190_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2212_ = l_Int_repr(v_num_2189_);
lean_dec(v_num_2189_);
v___x_2213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2));
v___x_2214_ = lean_string_append(v___x_2212_, v___x_2213_);
v___x_2215_ = l_Nat_reprFast(v_den_2190_);
v___x_2216_ = lean_string_append(v___x_2214_, v___x_2215_);
lean_dec_ref(v___x_2215_);
v___y_2199_ = v___x_2216_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2217_; 
lean_dec(v_den_2190_);
v___x_2217_ = l_Int_repr(v_num_2189_);
lean_dec(v_num_2189_);
v___y_2199_ = v___x_2217_;
goto v___jp_2198_;
}
v___jp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___y_2199_);
v___x_2201_ = l_Lean_MessageData_ofFormat(v___x_2200_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set_tag(v___x_2181_, 7);
lean_ctor_set(v___x_2181_, 1, v___x_2201_);
lean_ctor_set(v___x_2181_, 0, v___x_2197_);
v___x_2203_ = v___x_2181_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; 
v___x_2204_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2188_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
lean_ctor_set(v___x_2204_, 2, v___x_2183_);
v___x_2205_ = lean_array_push(v_b_2173_, v___x_2204_);
v___x_2206_ = ((size_t)1ULL);
v___x_2207_ = lean_usize_add(v_i_2172_, v___x_2206_);
v_i_2172_ = v___x_2207_;
v_b_2173_ = v___x_2205_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___boxed(lean_object* v_as_2221_, lean_object* v_sz_2222_, lean_object* v_i_2223_, lean_object* v_b_2224_, lean_object* v___y_2225_){
_start:
{
size_t v_sz_boxed_2226_; size_t v_i_boxed_2227_; lean_object* v_res_2228_; 
v_sz_boxed_2226_ = lean_unbox_usize(v_sz_2222_);
lean_dec(v_sz_2222_);
v_i_boxed_2227_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_res_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_2221_, v_sz_boxed_2226_, v_i_boxed_2227_, v_b_2224_);
lean_dec_ref(v_as_2221_);
return v_res_2228_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2(void){
_start:
{
lean_object* v___x_2232_; uint8_t v___x_2233_; double v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2232_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2233_ = 1;
v___x_2234_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2235_ = lean_box(0);
v___x_2236_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1));
v___x_2237_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v___x_2235_);
lean_ctor_set(v___x_2237_, 2, v___x_2232_);
lean_ctor_set_float(v___x_2237_, sizeof(void*)*3, v___x_2234_);
lean_ctor_set_float(v___x_2237_, sizeof(void*)*3 + 8, v___x_2234_);
lean_ctor_set_uint8(v___x_2237_, sizeof(void*)*3 + 16, v___x_2233_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4));
v___x_2242_ = l_Lean_MessageData_ofFormat(v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(lean_object* v_goal_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2250_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2249_, v_goal_2243_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2306_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2306_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2306_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v_varMap_2255_; uint8_t v___x_2256_; 
v_varMap_2255_ = lean_ctor_get(v_a_2251_, 1);
lean_inc_ref(v_varMap_2255_);
lean_dec(v_a_2251_);
v___x_2256_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_varMap_2255_);
lean_dec_ref(v_varMap_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
lean_del_object(v___x_2253_);
v___x_2257_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2293_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2293_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2293_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2262_ = lean_array_get_size(v_a_2258_);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_nat_dec_eq(v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; size_t v_sz_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
lean_del_object(v___x_2260_);
v___x_2265_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v_sz_2266_ = lean_array_size(v_a_2258_);
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_a_2258_, v_sz_2266_, v___x_2267_, v___x_2265_);
lean_dec(v_a_2258_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2280_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2280_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2280_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2273_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2);
v___x_2274_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5);
v___x_2275_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2273_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
lean_ctor_set(v___x_2275_, 2, v_a_2269_);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2276_);
v___x_2278_ = v___x_2271_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2268_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2268_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
lean_dec(v_a_2258_);
v___x_2289_ = lean_box(0);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2289_);
v___x_2291_ = v___x_2260_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
v_a_2294_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2257_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2257_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = lean_box(0);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2302_);
v___x_2304_ = v___x_2253_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2319_; 
v_a_2307_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2309_ = v___x_2250_;
v_isShared_2310_ = v_isSharedCheck_2319_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2250_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2319_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_ref_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v_ref_2311_ = lean_ctor_get(v_a_2246_, 5);
v___x_2312_ = lean_io_error_to_string(v_a_2307_);
v___x_2313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
v___x_2314_ = l_Lean_MessageData_ofFormat(v___x_2313_);
lean_inc(v_ref_2311_);
v___x_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2315_, 0, v_ref_2311_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2315_);
v___x_2317_ = v___x_2309_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___boxed(lean_object* v_goal_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(v_goal_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec_ref(v_goal_2320_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(lean_object* v_as_2327_, size_t v_sz_2328_, size_t v_i_2329_, lean_object* v_b_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_2327_, v_sz_2328_, v_i_2329_, v_b_2330_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___boxed(lean_object* v_as_2337_, lean_object* v_sz_2338_, lean_object* v_i_2339_, lean_object* v_b_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
size_t v_sz_boxed_2346_; size_t v_i_boxed_2347_; lean_object* v_res_2348_; 
v_sz_boxed_2346_ = lean_unbox_usize(v_sz_2338_);
lean_dec(v_sz_2338_);
v_i_boxed_2347_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_res_2348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(v_as_2337_, v_sz_boxed_2346_, v_i_boxed_2347_, v_b_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_as_2337_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(v_a_2349_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2368_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2368_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2368_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
if (lean_obj_tag(v_a_2357_) == 1)
{
lean_object* v_val_2361_; lean_object* v___x_2362_; 
lean_del_object(v___x_2359_);
v_val_2361_ = lean_ctor_get(v_a_2357_, 0);
lean_inc(v_val_2361_);
lean_dec_ref_known(v_a_2357_, 1);
v___x_2362_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2361_, v_a_2350_);
return v___x_2362_;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
lean_dec(v_a_2357_);
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
lean_ctor_set(v___x_2364_, 1, v_a_2350_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2364_);
v___x_2366_ = v___x_2359_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_a_2350_);
v_a_2369_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2356_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2356_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat___boxed(lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_a_2377_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(v_a_2385_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2404_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2404_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2404_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
if (lean_obj_tag(v_a_2393_) == 1)
{
lean_object* v_val_2397_; lean_object* v___x_2398_; 
lean_del_object(v___x_2395_);
v_val_2397_ = lean_ctor_get(v_a_2393_, 0);
lean_inc(v_val_2397_);
lean_dec_ref_known(v_a_2393_, 1);
v___x_2398_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2397_, v_a_2386_);
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
lean_dec(v_a_2393_);
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
lean_ctor_set(v___x_2400_, 1, v_a_2386_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2400_);
v___x_2402_ = v___x_2395_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v_a_2386_);
v_a_2405_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2392_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2392_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing___boxed(lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec_ref(v_a_2413_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_a_2421_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2440_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2440_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2440_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
if (lean_obj_tag(v_a_2429_) == 1)
{
lean_object* v_val_2433_; lean_object* v___x_2434_; 
lean_del_object(v___x_2431_);
v_val_2433_ = lean_ctor_get(v_a_2429_, 0);
lean_inc(v_val_2433_);
lean_dec_ref_known(v_a_2429_, 1);
v___x_2434_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2433_, v_a_2422_);
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2438_; 
lean_dec(v_a_2429_);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v_a_2422_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v___x_2436_);
v___x_2438_ = v___x_2431_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v_a_2422_);
v_a_2441_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2428_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2428_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith___boxed(lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec_ref(v_a_2449_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_Meta_Grind_AC_pp_x3f(v_a_2457_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2476_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2476_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2476_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
if (lean_obj_tag(v_a_2465_) == 1)
{
lean_object* v_val_2469_; lean_object* v___x_2470_; 
lean_del_object(v___x_2467_);
v_val_2469_ = lean_ctor_get(v_a_2465_, 0);
lean_inc(v_val_2469_);
lean_dec_ref_known(v_a_2465_, 1);
v___x_2470_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2469_, v_a_2458_);
return v___x_2470_;
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_a_2465_);
v___x_2471_ = lean_box(0);
v___x_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
lean_ctor_set(v___x_2472_, 1, v_a_2458_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2472_);
v___x_2474_ = v___x_2467_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_a_2458_);
v_a_2477_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2464_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2464_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC___boxed(lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec_ref(v_a_2485_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(lean_object* v_a_2493_, lean_object* v_as_2494_, size_t v_i_2495_, size_t v_stop_2496_, lean_object* v_b_2497_){
_start:
{
lean_object* v___y_2499_; uint8_t v___x_2503_; 
v___x_2503_ = lean_usize_dec_eq(v_i_2495_, v_stop_2496_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_array_uget_borrowed(v_as_2494_, v_i_2495_);
v___x_2505_ = l_Lean_Meta_Grind_Goal_getENode_x3f(v_a_2493_, v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 1)
{
lean_object* v_val_2506_; lean_object* v_generation_2507_; uint8_t v___x_2508_; 
v_val_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_val_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v_generation_2507_ = lean_ctor_get(v_val_2506_, 8);
lean_inc(v_generation_2507_);
lean_dec(v_val_2506_);
v___x_2508_ = lean_nat_dec_le(v_b_2497_, v_generation_2507_);
if (v___x_2508_ == 0)
{
lean_dec(v_generation_2507_);
v___y_2499_ = v_b_2497_;
goto v___jp_2498_;
}
else
{
lean_dec(v_b_2497_);
v___y_2499_ = v_generation_2507_;
goto v___jp_2498_;
}
}
else
{
lean_dec(v___x_2505_);
v___y_2499_ = v_b_2497_;
goto v___jp_2498_;
}
}
else
{
return v_b_2497_;
}
v___jp_2498_:
{
size_t v___x_2500_; size_t v___x_2501_; 
v___x_2500_ = ((size_t)1ULL);
v___x_2501_ = lean_usize_add(v_i_2495_, v___x_2500_);
v_i_2495_ = v___x_2501_;
v_b_2497_ = v___y_2499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1___boxed(lean_object* v_a_2509_, lean_object* v_as_2510_, lean_object* v_i_2511_, lean_object* v_stop_2512_, lean_object* v_b_2513_){
_start:
{
size_t v_i_boxed_2514_; size_t v_stop_boxed_2515_; lean_object* v_res_2516_; 
v_i_boxed_2514_ = lean_unbox_usize(v_i_2511_);
lean_dec(v_i_2511_);
v_stop_boxed_2515_ = lean_unbox_usize(v_stop_2512_);
lean_dec(v_stop_2512_);
v_res_2516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2509_, v_as_2510_, v_i_boxed_2514_, v_stop_boxed_2515_, v_b_2513_);
lean_dec_ref(v_as_2510_);
lean_dec_ref(v_a_2509_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(lean_object* v_a_2517_, lean_object* v_x_2518_, lean_object* v_x_2519_){
_start:
{
if (lean_obj_tag(v_x_2518_) == 0)
{
lean_object* v_cs_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v_cs_2520_ = lean_ctor_get(v_x_2518_, 0);
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = lean_array_get_size(v_cs_2520_);
v___x_2523_ = lean_nat_dec_lt(v___x_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
return v_x_2519_;
}
else
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_nat_dec_le(v___x_2522_, v___x_2522_);
if (v___x_2524_ == 0)
{
if (v___x_2523_ == 0)
{
return v_x_2519_;
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2522_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2517_, v_cs_2520_, v___x_2525_, v___x_2526_, v_x_2519_);
return v___x_2527_;
}
}
else
{
size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = lean_usize_of_nat(v___x_2522_);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2517_, v_cs_2520_, v___x_2528_, v___x_2529_, v_x_2519_);
return v___x_2530_;
}
}
}
else
{
lean_object* v_vs_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_vs_2531_ = lean_ctor_get(v_x_2518_, 0);
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = lean_array_get_size(v_vs_2531_);
v___x_2534_ = lean_nat_dec_lt(v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
return v_x_2519_;
}
else
{
uint8_t v___x_2535_; 
v___x_2535_ = lean_nat_dec_le(v___x_2533_, v___x_2533_);
if (v___x_2535_ == 0)
{
if (v___x_2534_ == 0)
{
return v_x_2519_;
}
else
{
size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = ((size_t)0ULL);
v___x_2537_ = lean_usize_of_nat(v___x_2533_);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2517_, v_vs_2531_, v___x_2536_, v___x_2537_, v_x_2519_);
return v___x_2538_;
}
}
else
{
size_t v___x_2539_; size_t v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = lean_usize_of_nat(v___x_2533_);
v___x_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2517_, v_vs_2531_, v___x_2539_, v___x_2540_, v_x_2519_);
return v___x_2541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(lean_object* v_a_2542_, lean_object* v_as_2543_, size_t v_i_2544_, size_t v_stop_2545_, lean_object* v_b_2546_){
_start:
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_usize_dec_eq(v_i_2544_, v_stop_2545_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; 
v___x_2548_ = lean_array_uget_borrowed(v_as_2543_, v_i_2544_);
v___x_2549_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2542_, v___x_2548_, v_b_2546_);
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_add(v_i_2544_, v___x_2550_);
v_i_2544_ = v___x_2551_;
v_b_2546_ = v___x_2549_;
goto _start;
}
else
{
return v_b_2546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1___boxed(lean_object* v_a_2553_, lean_object* v_as_2554_, lean_object* v_i_2555_, lean_object* v_stop_2556_, lean_object* v_b_2557_){
_start:
{
size_t v_i_boxed_2558_; size_t v_stop_boxed_2559_; lean_object* v_res_2560_; 
v_i_boxed_2558_ = lean_unbox_usize(v_i_2555_);
lean_dec(v_i_2555_);
v_stop_boxed_2559_ = lean_unbox_usize(v_stop_2556_);
lean_dec(v_stop_2556_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2553_, v_as_2554_, v_i_boxed_2558_, v_stop_boxed_2559_, v_b_2557_);
lean_dec_ref(v_as_2554_);
lean_dec_ref(v_a_2553_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2___boxed(lean_object* v_a_2561_, lean_object* v_x_2562_, lean_object* v_x_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2561_, v_x_2562_, v_x_2563_);
lean_dec_ref(v_x_2562_);
lean_dec_ref(v_a_2561_);
return v_res_2564_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(lean_object* v_a_2566_, lean_object* v_x_2567_, size_t v_x_2568_, size_t v_x_2569_, lean_object* v_x_2570_){
_start:
{
if (lean_obj_tag(v_x_2567_) == 0)
{
lean_object* v_cs_2571_; lean_object* v___x_2572_; size_t v___x_2573_; lean_object* v_j_2574_; lean_object* v___x_2575_; size_t v___x_2576_; size_t v___x_2577_; size_t v___x_2578_; size_t v___x_2579_; size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v_cs_2571_ = lean_ctor_get(v_x_2567_, 0);
v___x_2572_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0);
v___x_2573_ = lean_usize_shift_right(v_x_2568_, v_x_2569_);
v_j_2574_ = lean_usize_to_nat(v___x_2573_);
v___x_2575_ = lean_array_get_borrowed(v___x_2572_, v_cs_2571_, v_j_2574_);
v___x_2576_ = ((size_t)1ULL);
v___x_2577_ = lean_usize_shift_left(v___x_2576_, v_x_2569_);
v___x_2578_ = lean_usize_sub(v___x_2577_, v___x_2576_);
v___x_2579_ = lean_usize_land(v_x_2568_, v___x_2578_);
v___x_2580_ = ((size_t)5ULL);
v___x_2581_ = lean_usize_sub(v_x_2569_, v___x_2580_);
v___x_2582_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2566_, v___x_2575_, v___x_2579_, v___x_2581_, v_x_2570_);
v___x_2583_ = lean_unsigned_to_nat(1u);
v___x_2584_ = lean_nat_add(v_j_2574_, v___x_2583_);
lean_dec(v_j_2574_);
v___x_2585_ = lean_array_get_size(v_cs_2571_);
v___x_2586_ = lean_nat_dec_lt(v___x_2584_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_dec(v___x_2584_);
return v___x_2582_;
}
else
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_nat_dec_le(v___x_2585_, v___x_2585_);
if (v___x_2587_ == 0)
{
if (v___x_2586_ == 0)
{
lean_dec(v___x_2584_);
return v___x_2582_;
}
else
{
size_t v___x_2588_; size_t v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_usize_of_nat(v___x_2584_);
lean_dec(v___x_2584_);
v___x_2589_ = lean_usize_of_nat(v___x_2585_);
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2566_, v_cs_2571_, v___x_2588_, v___x_2589_, v___x_2582_);
return v___x_2590_;
}
}
else
{
size_t v___x_2591_; size_t v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_usize_of_nat(v___x_2584_);
lean_dec(v___x_2584_);
v___x_2592_ = lean_usize_of_nat(v___x_2585_);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2566_, v_cs_2571_, v___x_2591_, v___x_2592_, v___x_2582_);
return v___x_2593_;
}
}
}
else
{
lean_object* v_vs_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_vs_2594_ = lean_ctor_get(v_x_2567_, 0);
v___x_2595_ = lean_usize_to_nat(v_x_2568_);
v___x_2596_ = lean_array_get_size(v_vs_2594_);
v___x_2597_ = lean_nat_dec_lt(v___x_2595_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_dec(v___x_2595_);
return v_x_2570_;
}
else
{
uint8_t v___x_2598_; 
v___x_2598_ = lean_nat_dec_le(v___x_2596_, v___x_2596_);
if (v___x_2598_ == 0)
{
if (v___x_2597_ == 0)
{
lean_dec(v___x_2595_);
return v_x_2570_;
}
else
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_usize_of_nat(v___x_2595_);
lean_dec(v___x_2595_);
v___x_2600_ = lean_usize_of_nat(v___x_2596_);
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2566_, v_vs_2594_, v___x_2599_, v___x_2600_, v_x_2570_);
return v___x_2601_;
}
}
else
{
size_t v___x_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_usize_of_nat(v___x_2595_);
lean_dec(v___x_2595_);
v___x_2603_ = lean_usize_of_nat(v___x_2596_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2566_, v_vs_2594_, v___x_2602_, v___x_2603_, v_x_2570_);
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___boxed(lean_object* v_a_2605_, lean_object* v_x_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_, lean_object* v_x_2609_){
_start:
{
size_t v_x_5395__boxed_2610_; size_t v_x_5396__boxed_2611_; lean_object* v_res_2612_; 
v_x_5395__boxed_2610_ = lean_unbox_usize(v_x_2607_);
lean_dec(v_x_2607_);
v_x_5396__boxed_2611_ = lean_unbox_usize(v_x_2608_);
lean_dec(v_x_2608_);
v_res_2612_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2605_, v_x_2606_, v_x_5395__boxed_2610_, v_x_5396__boxed_2611_, v_x_2609_);
lean_dec_ref(v_x_2606_);
lean_dec_ref(v_a_2605_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(lean_object* v_a_2613_, lean_object* v_t_2614_, lean_object* v_init_2615_, lean_object* v_start_2616_){
_start:
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = lean_unsigned_to_nat(0u);
v___x_2618_ = lean_nat_dec_eq(v_start_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v_root_2619_; lean_object* v_tail_2620_; size_t v_shift_2621_; lean_object* v_tailOff_2622_; uint8_t v___x_2623_; 
v_root_2619_ = lean_ctor_get(v_t_2614_, 0);
v_tail_2620_ = lean_ctor_get(v_t_2614_, 1);
v_shift_2621_ = lean_ctor_get_usize(v_t_2614_, 4);
v_tailOff_2622_ = lean_ctor_get(v_t_2614_, 3);
v___x_2623_ = lean_nat_dec_le(v_tailOff_2622_, v_start_2616_);
if (v___x_2623_ == 0)
{
size_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2624_ = lean_usize_of_nat(v_start_2616_);
v___x_2625_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2613_, v_root_2619_, v___x_2624_, v_shift_2621_, v_init_2615_);
v___x_2626_ = lean_array_get_size(v_tail_2620_);
v___x_2627_ = lean_nat_dec_lt(v___x_2617_, v___x_2626_);
if (v___x_2627_ == 0)
{
return v___x_2625_;
}
else
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_nat_dec_le(v___x_2626_, v___x_2626_);
if (v___x_2628_ == 0)
{
if (v___x_2627_ == 0)
{
return v___x_2625_;
}
else
{
size_t v___x_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = ((size_t)0ULL);
v___x_2630_ = lean_usize_of_nat(v___x_2626_);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2613_, v_tail_2620_, v___x_2629_, v___x_2630_, v___x_2625_);
return v___x_2631_;
}
}
else
{
size_t v___x_2632_; size_t v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = ((size_t)0ULL);
v___x_2633_ = lean_usize_of_nat(v___x_2626_);
v___x_2634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2613_, v_tail_2620_, v___x_2632_, v___x_2633_, v___x_2625_);
return v___x_2634_;
}
}
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2635_ = lean_nat_sub(v_start_2616_, v_tailOff_2622_);
v___x_2636_ = lean_array_get_size(v_tail_2620_);
v___x_2637_ = lean_nat_dec_lt(v___x_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_dec(v___x_2635_);
return v_init_2615_;
}
else
{
uint8_t v___x_2638_; 
v___x_2638_ = lean_nat_dec_le(v___x_2636_, v___x_2636_);
if (v___x_2638_ == 0)
{
if (v___x_2637_ == 0)
{
lean_dec(v___x_2635_);
return v_init_2615_;
}
else
{
size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_usize_of_nat(v___x_2635_);
lean_dec(v___x_2635_);
v___x_2640_ = lean_usize_of_nat(v___x_2636_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2613_, v_tail_2620_, v___x_2639_, v___x_2640_, v_init_2615_);
return v___x_2641_;
}
}
else
{
size_t v___x_2642_; size_t v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_usize_of_nat(v___x_2635_);
lean_dec(v___x_2635_);
v___x_2643_ = lean_usize_of_nat(v___x_2636_);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2613_, v_tail_2620_, v___x_2642_, v___x_2643_, v_init_2615_);
return v___x_2644_;
}
}
}
}
else
{
lean_object* v_root_2645_; lean_object* v_tail_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_root_2645_ = lean_ctor_get(v_t_2614_, 0);
v_tail_2646_ = lean_ctor_get(v_t_2614_, 1);
v___x_2647_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2613_, v_root_2645_, v_init_2615_);
v___x_2648_ = lean_array_get_size(v_tail_2646_);
v___x_2649_ = lean_nat_dec_lt(v___x_2617_, v___x_2648_);
if (v___x_2649_ == 0)
{
return v___x_2647_;
}
else
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_nat_dec_le(v___x_2648_, v___x_2648_);
if (v___x_2650_ == 0)
{
if (v___x_2649_ == 0)
{
return v___x_2647_;
}
else
{
size_t v___x_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = ((size_t)0ULL);
v___x_2652_ = lean_usize_of_nat(v___x_2648_);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2613_, v_tail_2646_, v___x_2651_, v___x_2652_, v___x_2647_);
return v___x_2653_;
}
}
else
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = lean_usize_of_nat(v___x_2648_);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2613_, v_tail_2646_, v___x_2654_, v___x_2655_, v___x_2647_);
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0___boxed(lean_object* v_a_2657_, lean_object* v_t_2658_, lean_object* v_init_2659_, lean_object* v_start_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_2657_, v_t_2658_, v_init_2659_, v_start_2660_);
lean_dec(v_start_2660_);
lean_dec_ref(v_t_2658_);
lean_dec_ref(v_a_2657_);
return v_res_2661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2(void){
_start:
{
lean_object* v___x_2665_; uint8_t v___x_2666_; double v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2665_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2666_ = 1;
v___x_2667_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2668_ = lean_box(0);
v___x_2669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1));
v___x_2670_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___x_2668_);
lean_ctor_set(v___x_2670_, 2, v___x_2665_);
lean_ctor_set_float(v___x_2670_, sizeof(void*)*3, v___x_2667_);
lean_ctor_set_float(v___x_2670_, sizeof(void*)*3 + 8, v___x_2667_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*3 + 16, v___x_2666_);
return v___x_2670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4));
v___x_2675_ = l_Lean_MessageData_ofFormat(v___x_2674_);
return v___x_2675_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8));
v___x_2681_ = l_Lean_stringToMessageData(v___x_2680_);
return v___x_2681_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10));
v___x_2684_ = l_Lean_stringToMessageData(v___x_2683_);
return v___x_2684_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12));
v___x_2687_ = l_Lean_stringToMessageData(v___x_2686_);
return v___x_2687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14));
v___x_2690_ = l_Lean_stringToMessageData(v___x_2689_);
return v___x_2690_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16));
v___x_2693_ = l_Lean_stringToMessageData(v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(lean_object* v_c_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_toGoalState_2699_; lean_object* v_exprs_2700_; lean_object* v_ematch_2701_; lean_object* v_split_2702_; lean_object* v___x_2703_; lean_object* v_msgs_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___x_2738_; lean_object* v_splits_2739_; lean_object* v_ematch_2740_; lean_object* v_gen_2741_; lean_object* v_instances_2742_; lean_object* v_numInstances_2743_; lean_object* v_num_2744_; lean_object* v___x_2745_; lean_object* v_msgs_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v_msgs_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v_msgs_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; uint8_t v___x_2804_; 
v_toGoalState_2699_ = lean_ctor_get(v_a_2695_, 0);
v_exprs_2700_ = lean_ctor_get(v_toGoalState_2699_, 2);
v_ematch_2701_ = lean_ctor_get(v_toGoalState_2699_, 12);
v_split_2702_ = lean_ctor_get(v_toGoalState_2699_, 14);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2738_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_2695_, v_exprs_2700_, v___x_2703_, v___x_2703_);
v_splits_2739_ = lean_ctor_get(v_c_2694_, 0);
v_ematch_2740_ = lean_ctor_get(v_c_2694_, 1);
v_gen_2741_ = lean_ctor_get(v_c_2694_, 2);
v_instances_2742_ = lean_ctor_get(v_c_2694_, 4);
v_numInstances_2743_ = lean_ctor_get(v_ematch_2701_, 4);
v_num_2744_ = lean_ctor_get(v_ematch_2701_, 6);
v___x_2745_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2804_ = lean_nat_dec_le(v_instances_2742_, v_numInstances_2743_);
if (v___x_2804_ == 0)
{
v_msgs_2786_ = v___x_2745_;
v___y_2787_ = v_a_2696_;
v___y_2788_ = v_a_2697_;
goto v___jp_2785_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; double v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2806_ = lean_box(0);
v___x_2807_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2808_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2809_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2809_, 0, v___x_2805_);
lean_ctor_set(v___x_2809_, 1, v___x_2806_);
lean_ctor_set(v___x_2809_, 2, v___x_2808_);
lean_ctor_set_float(v___x_2809_, sizeof(void*)*3, v___x_2807_);
lean_ctor_set_float(v___x_2809_, sizeof(void*)*3 + 8, v___x_2807_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*3 + 16, v___x_2804_);
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17);
lean_inc(v_instances_2742_);
v___x_2811_ = l_Nat_reprFast(v_instances_2742_);
v___x_2812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
v___x_2813_ = l_Lean_MessageData_ofFormat(v___x_2812_);
v___x_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2810_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2809_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
lean_ctor_set(v___x_2817_, 2, v___x_2745_);
v___x_2818_ = lean_array_push(v___x_2745_, v___x_2817_);
v_msgs_2786_ = v___x_2818_;
v___y_2787_ = v_a_2696_;
v___y_2788_ = v_a_2697_;
goto v___jp_2785_;
}
v___jp_2704_:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(v_a_2695_, v_c_2694_, v_msgs_2705_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2724_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2724_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2724_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = lean_array_get_size(v_a_2709_);
v___x_2714_ = lean_nat_dec_eq(v___x_2713_, v___x_2703_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_del_object(v___x_2711_);
v___x_2715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2);
v___x_2716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5);
v___x_2717_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
lean_ctor_set(v___x_2717_, 2, v_a_2709_);
v___x_2718_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2717_, v___y_2706_);
return v___x_2718_;
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
lean_dec(v_a_2709_);
v___x_2719_ = lean_box(0);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___y_2706_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2720_);
v___x_2722_ = v___x_2711_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v___y_2706_);
v_a_2725_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2727_ = v___x_2708_;
v_isShared_2728_ = v_isSharedCheck_2737_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2708_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2737_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_ref_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v_ref_2729_ = lean_ctor_get(v___y_2707_, 5);
v___x_2730_ = lean_io_error_to_string(v_a_2725_);
v___x_2731_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
v___x_2732_ = l_Lean_MessageData_ofFormat(v___x_2731_);
lean_inc(v_ref_2729_);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v_ref_2729_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2733_);
v___x_2735_ = v___x_2727_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
v___jp_2746_:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_nat_dec_le(v_gen_2741_, v___x_2738_);
lean_dec(v___x_2738_);
if (v___x_2750_ == 0)
{
v_msgs_2705_ = v_msgs_2747_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; double v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2754_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2755_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2755_, 0, v___x_2751_);
lean_ctor_set(v___x_2755_, 1, v___x_2752_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
lean_ctor_set_float(v___x_2755_, sizeof(void*)*3, v___x_2753_);
lean_ctor_set_float(v___x_2755_, sizeof(void*)*3 + 8, v___x_2753_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*3 + 16, v___x_2750_);
v___x_2756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9);
lean_inc(v_gen_2741_);
v___x_2757_ = l_Nat_reprFast(v_gen_2741_);
v___x_2758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
v___x_2759_ = l_Lean_MessageData_ofFormat(v___x_2758_);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2756_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2755_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
lean_ctor_set(v___x_2763_, 2, v___x_2745_);
v___x_2764_ = lean_array_push(v_msgs_2747_, v___x_2763_);
v_msgs_2705_ = v___x_2764_;
v___y_2706_ = v___y_2748_;
v___y_2707_ = v___y_2749_;
goto v___jp_2704_;
}
}
v___jp_2765_:
{
lean_object* v_num_2769_; uint8_t v___x_2770_; 
v_num_2769_ = lean_ctor_get(v_split_2702_, 0);
v___x_2770_ = lean_nat_dec_le(v_splits_2739_, v_num_2769_);
if (v___x_2770_ == 0)
{
v_msgs_2747_ = v_msgs_2766_;
v___y_2748_ = v___y_2767_;
v___y_2749_ = v___y_2768_;
goto v___jp_2746_;
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; double v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2774_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2775_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2775_, 0, v___x_2771_);
lean_ctor_set(v___x_2775_, 1, v___x_2772_);
lean_ctor_set(v___x_2775_, 2, v___x_2774_);
lean_ctor_set_float(v___x_2775_, sizeof(void*)*3, v___x_2773_);
lean_ctor_set_float(v___x_2775_, sizeof(void*)*3 + 8, v___x_2773_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*3 + 16, v___x_2770_);
v___x_2776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13);
lean_inc(v_splits_2739_);
v___x_2777_ = l_Nat_reprFast(v_splits_2739_);
v___x_2778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
v___x_2779_ = l_Lean_MessageData_ofFormat(v___x_2778_);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2776_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2775_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
lean_ctor_set(v___x_2783_, 2, v___x_2745_);
v___x_2784_ = lean_array_push(v_msgs_2766_, v___x_2783_);
v_msgs_2747_ = v___x_2784_;
v___y_2748_ = v___y_2767_;
v___y_2749_ = v___y_2768_;
goto v___jp_2746_;
}
}
v___jp_2785_:
{
uint8_t v___x_2789_; 
v___x_2789_ = lean_nat_dec_le(v_ematch_2740_, v_num_2744_);
if (v___x_2789_ == 0)
{
v_msgs_2766_ = v_msgs_2786_;
v___y_2767_ = v___y_2787_;
v___y_2768_ = v___y_2788_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; double v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2791_ = lean_box(0);
v___x_2792_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2793_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2794_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2794_, 0, v___x_2790_);
lean_ctor_set(v___x_2794_, 1, v___x_2791_);
lean_ctor_set(v___x_2794_, 2, v___x_2793_);
lean_ctor_set_float(v___x_2794_, sizeof(void*)*3, v___x_2792_);
lean_ctor_set_float(v___x_2794_, sizeof(void*)*3 + 8, v___x_2792_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*3 + 16, v___x_2789_);
v___x_2795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15);
lean_inc(v_ematch_2740_);
v___x_2796_ = l_Nat_reprFast(v_ematch_2740_);
v___x_2797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
v___x_2798_ = l_Lean_MessageData_ofFormat(v___x_2797_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2795_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2794_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
lean_ctor_set(v___x_2802_, 2, v___x_2745_);
v___x_2803_ = lean_array_push(v_msgs_2786_, v___x_2802_);
v_msgs_2766_ = v___x_2803_;
v___y_2767_ = v___y_2787_;
v___y_2768_ = v___y_2788_;
goto v___jp_2765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___boxed(lean_object* v_c_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_c_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec_ref(v_a_2822_);
lean_dec_ref(v_a_2820_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(lean_object* v_c_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_c_2825_, v_a_2826_, v_a_2827_, v_a_2830_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___boxed(lean_object* v_c_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(v_c_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec_ref(v_a_2835_);
return v_res_2842_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2846_; uint8_t v___x_2847_; double v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2846_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2847_ = 1;
v___x_2848_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2849_ = lean_box(0);
v___x_2850_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1));
v___x_2851_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
lean_ctor_set(v___x_2851_, 1, v___x_2849_);
lean_ctor_set(v___x_2851_, 2, v___x_2846_);
lean_ctor_set_float(v___x_2851_, sizeof(void*)*3, v___x_2848_);
lean_ctor_set_float(v___x_2851_, sizeof(void*)*3 + 8, v___x_2848_);
lean_ctor_set_uint8(v___x_2851_, sizeof(void*)*3 + 16, v___x_2847_);
return v___x_2851_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3));
v___x_2854_ = l_Lean_stringToMessageData(v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2));
v___x_2856_ = l_Lean_stringToMessageData(v___x_2855_);
return v___x_2856_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6));
v___x_2859_ = l_Lean_stringToMessageData(v___x_2858_);
return v___x_2859_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8));
v___x_2862_ = l_Lean_stringToMessageData(v___x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(lean_object* v_as_x27_2863_, lean_object* v_b_2864_, lean_object* v___y_2865_){
_start:
{
if (lean_obj_tag(v_as_x27_2863_) == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v_b_2864_);
lean_ctor_set(v___x_2867_, 1, v___y_2865_);
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
return v___x_2868_;
}
else
{
lean_object* v_head_2869_; lean_object* v_tail_2870_; lean_object* v_expr_2871_; lean_object* v_i_2872_; lean_object* v_num_2873_; lean_object* v_source_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_head_2869_ = lean_ctor_get(v_as_x27_2863_, 0);
v_tail_2870_ = lean_ctor_get(v_as_x27_2863_, 1);
v_expr_2871_ = lean_ctor_get(v_head_2869_, 0);
v_i_2872_ = lean_ctor_get(v_head_2869_, 1);
v_num_2873_ = lean_ctor_get(v_head_2869_, 2);
v_source_2874_ = lean_ctor_get(v_head_2869_, 3);
v___x_2875_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2876_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
v___x_2877_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4);
v___x_2878_ = lean_unsigned_to_nat(1u);
v___x_2879_ = lean_nat_add(v_i_2872_, v___x_2878_);
v___x_2880_ = l_Nat_reprFast(v___x_2879_);
v___x_2881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
v___x_2882_ = l_Lean_MessageData_ofFormat(v___x_2881_);
v___x_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2877_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
lean_inc(v_num_2873_);
v___x_2886_ = l_Nat_reprFast(v_num_2873_);
v___x_2887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
v___x_2888_ = l_Lean_MessageData_ofFormat(v___x_2887_);
v___x_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2885_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7);
v___x_2891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
lean_inc_ref(v_expr_2871_);
v___x_2892_ = l_Lean_MessageData_ofExpr(v_expr_2871_);
v___x_2893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9);
lean_inc(v_source_2874_);
v___x_2895_ = l_Lean_Meta_Grind_SplitSource_toMessageData(v_source_2874_);
v___x_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2876_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
lean_ctor_set(v___x_2897_, 2, v___x_2875_);
v___x_2898_ = lean_mk_empty_array_with_capacity(v___x_2878_);
v___x_2899_ = lean_array_push(v___x_2898_, v___x_2897_);
v___x_2900_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2876_);
lean_ctor_set(v___x_2900_, 1, v___x_2893_);
lean_ctor_set(v___x_2900_, 2, v___x_2899_);
v___x_2901_ = lean_array_push(v_b_2864_, v___x_2900_);
v_as_x27_2863_ = v_tail_2870_;
v_b_2864_ = v___x_2901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___boxed(lean_object* v_as_x27_2903_, lean_object* v_b_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_2903_, v_b_2904_, v___y_2905_);
lean_dec(v_as_x27_2903_);
return v_res_2907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1));
v___x_2912_ = l_Lean_MessageData_ofFormat(v___x_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_toGoalState_2920_; lean_object* v_split_2921_; lean_object* v_trace_2922_; uint8_t v___x_2923_; 
v_toGoalState_2920_ = lean_ctor_get(v_a_2913_, 0);
v_split_2921_ = lean_ctor_get(v_toGoalState_2920_, 14);
v_trace_2922_ = lean_ctor_get(v_split_2921_, 4);
v___x_2923_ = l_List_isEmpty___redArg(v_trace_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v_a_2927_; lean_object* v_fst_2928_; lean_object* v_snd_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2924_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
lean_inc(v_trace_2922_);
v___x_2925_ = l_List_reverse___redArg(v_trace_2922_);
v___x_2926_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v___x_2925_, v___x_2924_, v_a_2914_);
lean_dec(v___x_2925_);
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref(v___x_2926_);
v_fst_2928_ = lean_ctor_get(v_a_2927_, 0);
lean_inc(v_fst_2928_);
v_snd_2929_ = lean_ctor_get(v_a_2927_, 1);
lean_inc(v_snd_2929_);
lean_dec(v_a_2927_);
v___x_2930_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
v___x_2931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2);
v___x_2932_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
lean_ctor_set(v___x_2932_, 2, v_fst_2928_);
v___x_2933_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2932_, v_snd_2929_);
return v___x_2933_;
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_box(0);
v___x_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v_a_2914_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___boxed(lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec_ref(v_a_2937_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(lean_object* v_as_2945_, lean_object* v_as_x27_2946_, lean_object* v_b_2947_, lean_object* v_a_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_2946_, v_b_2947_, v___y_2950_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___boxed(lean_object* v_as_2957_, lean_object* v_as_x27_2958_, lean_object* v_b_2959_, lean_object* v_a_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(v_as_2957_, v_as_x27_2958_, v_b_2959_, v_a_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v___y_2961_);
lean_dec(v_as_x27_2958_);
lean_dec(v_as_2957_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(lean_object* v_goal_2973_, lean_object* v_config_2974_, uint8_t v_collapsedMain_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_toGoalState_2983_; lean_object* v_facts_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v_snd_2992_; lean_object* v___x_2993_; 
v_toGoalState_2983_ = lean_ctor_get(v_goal_2973_, 0);
v_facts_2984_ = lean_ctor_get(v_toGoalState_2983_, 10);
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1));
v___x_2986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2));
v___x_2987_ = l_Lean_PersistentArray_toArray___redArg(v_facts_2984_);
v___x_2988_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_2989_ = l_Lean_Meta_Grind_ppExprArray(v___x_2985_, v___x_2986_, v___x_2987_, v___x_2988_, v_collapsedMain_2975_);
v___x_2990_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2989_, v_a_2977_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2990_);
v_snd_2992_ = lean_ctor_get(v_a_2991_, 1);
lean_inc(v_snd_2992_);
lean_dec(v_a_2991_);
v___x_2993_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(v_collapsedMain_2975_, v_a_2976_, v_snd_2992_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v_snd_2995_; lean_object* v___x_2996_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v_snd_2995_ = lean_ctor_get(v_a_2994_, 1);
lean_inc(v_snd_2995_);
lean_dec(v_a_2994_);
v___x_2996_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(v_a_2976_, v_snd_2995_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v_snd_2998_; lean_object* v___x_2999_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v_snd_2998_ = lean_ctor_get(v_a_2997_, 1);
lean_inc(v_snd_2998_);
lean_dec(v_a_2997_);
v___x_2999_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(v_a_2976_, v_snd_2998_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v_snd_3001_; lean_object* v___x_3002_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v_snd_3001_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_snd_3001_);
lean_dec(v_a_3000_);
v___x_3002_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(v_a_2976_, v_snd_3001_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v_snd_3004_; lean_object* v___x_3005_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v_snd_3004_ = lean_ctor_get(v_a_3003_, 1);
lean_inc(v_snd_3004_);
lean_dec(v_a_3003_);
v___x_3005_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(v_a_2976_, v_snd_3004_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v_snd_3007_; lean_object* v___x_3008_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v_snd_3007_ = lean_ctor_get(v_a_3006_, 1);
lean_inc(v_snd_3007_);
lean_dec(v_a_3006_);
v___x_3008_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(v_a_2976_, v_snd_3007_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v_snd_3010_; lean_object* v___x_3011_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v_snd_3010_ = lean_ctor_get(v_a_3009_, 1);
lean_inc(v_snd_3010_);
lean_dec(v_a_3009_);
v___x_3011_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(v_a_2976_, v_snd_3010_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v_snd_3013_; lean_object* v___x_3014_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v_snd_3013_ = lean_ctor_get(v_a_3012_, 1);
lean_inc(v_snd_3013_);
lean_dec(v_a_3012_);
v___x_3014_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_config_2974_, v_a_2976_, v_snd_3013_, v_a_2980_);
return v___x_3014_;
}
else
{
lean_dec_ref(v_config_2974_);
return v___x_3011_;
}
}
else
{
lean_dec_ref(v_config_2974_);
return v___x_3008_;
}
}
else
{
lean_dec_ref(v_config_2974_);
return v___x_3005_;
}
}
else
{
lean_dec_ref(v_config_2974_);
return v___x_3002_;
}
}
else
{
lean_dec_ref(v_config_2974_);
return v___x_2999_;
}
}
else
{
lean_dec_ref(v_config_2974_);
return v___x_2996_;
}
}
else
{
lean_dec_ref(v_config_2974_);
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___boxed(lean_object* v_goal_3015_, lean_object* v_config_3016_, lean_object* v_collapsedMain_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
uint8_t v_collapsedMain_boxed_3025_; lean_object* v_res_3026_; 
v_collapsedMain_boxed_3025_ = lean_unbox(v_collapsedMain_3017_);
v_res_3026_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_3015_, v_config_3016_, v_collapsedMain_boxed_3025_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec_ref(v_a_3018_);
lean_dec_ref(v_goal_3015_);
return v_res_3026_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2(void){
_start:
{
lean_object* v___x_3030_; uint8_t v___x_3031_; double v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3030_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_3031_ = 0;
v___x_3032_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_3033_ = lean_box(0);
v___x_3034_ = ((lean_object*)(l_Lean_Meta_Grind_goalDiagToMessageData___closed__1));
v___x_3035_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v___x_3033_);
lean_ctor_set(v___x_3035_, 2, v___x_3030_);
lean_ctor_set_float(v___x_3035_, sizeof(void*)*3, v___x_3032_);
lean_ctor_set_float(v___x_3035_, sizeof(void*)*3 + 8, v___x_3032_);
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*3 + 16, v___x_3031_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData(lean_object* v_goal_3036_, lean_object* v_config_3037_, lean_object* v_header_3038_, uint8_t v_collapsedMain_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_3046_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_3036_, v_config_3037_, v_collapsedMain_3039_, v_goal_3036_, v___x_3045_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3059_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3059_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3059_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_snd_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v_snd_3051_ = lean_ctor_get(v_a_3047_, 1);
lean_inc(v_snd_3051_);
lean_dec(v_a_3047_);
v___x_3052_ = lean_obj_once(&l_Lean_Meta_Grind_goalDiagToMessageData___closed__2, &l_Lean_Meta_Grind_goalDiagToMessageData___closed__2_once, _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2);
v___x_3053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3053_, 0, v_header_3038_);
v___x_3054_ = l_Lean_MessageData_ofFormat(v___x_3053_);
v___x_3055_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3052_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
lean_ctor_set(v___x_3055_, 2, v_snd_3051_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3055_);
v___x_3057_ = v___x_3049_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v_header_3038_);
v_a_3060_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3046_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3046_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___boxed(lean_object* v_goal_3068_, lean_object* v_config_3069_, lean_object* v_header_3070_, lean_object* v_collapsedMain_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
uint8_t v_collapsedMain_boxed_3077_; lean_object* v_res_3078_; 
v_collapsedMain_boxed_3077_ = lean_unbox(v_collapsedMain_3071_);
v_res_3078_ = l_Lean_Meta_Grind_goalDiagToMessageData(v_goal_3068_, v_config_3069_, v_header_3070_, v_collapsedMain_boxed_3077_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec_ref(v_goal_3068_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(lean_object* v_msgData_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; lean_object* v_env_3086_; lean_object* v___x_3087_; lean_object* v_mctx_3088_; lean_object* v_lctx_3089_; lean_object* v_options_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3085_ = lean_st_ref_get(v___y_3083_);
v_env_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc_ref(v_env_3086_);
lean_dec(v___x_3085_);
v___x_3087_ = lean_st_ref_get(v___y_3081_);
v_mctx_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc_ref(v_mctx_3088_);
lean_dec(v___x_3087_);
v_lctx_3089_ = lean_ctor_get(v___y_3080_, 2);
v_options_3090_ = lean_ctor_get(v___y_3082_, 2);
lean_inc_ref(v_options_3090_);
lean_inc_ref(v_lctx_3089_);
v___x_3091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3091_, 0, v_env_3086_);
lean_ctor_set(v___x_3091_, 1, v_mctx_3088_);
lean_ctor_set(v___x_3091_, 2, v_lctx_3089_);
lean_ctor_set(v___x_3091_, 3, v_options_3090_);
v___x_3092_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v_msgData_3079_);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0___boxed(lean_object* v_msgData_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(v_msgData_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(lean_object* v_mvarId_3101_, lean_object* v_x_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3101_, v_x_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
v_a_3117_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3108_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3108_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg___boxed(lean_object* v_mvarId_3125_, lean_object* v_x_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3125_, v_x_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(lean_object* v_00_u03b1_3133_, lean_object* v_mvarId_3134_, lean_object* v_x_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3134_, v_x_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___boxed(lean_object* v_00_u03b1_3142_, lean_object* v_mvarId_3143_, lean_object* v_x_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(v_00_u03b1_3142_, v_mvarId_3143_, v_x_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
return v_res_3150_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0));
v___x_3153_ = l_Lean_stringToMessageData(v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0(uint8_t v_verbose_3154_, lean_object* v_mvarId_3155_, lean_object* v_goal_3156_, lean_object* v_config_3157_, uint8_t v___x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
if (v_verbose_3154_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec_ref(v_config_3157_);
v___x_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_mvarId_3155_);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0));
v___x_3167_ = l_Lean_Meta_Grind_goalDiagToMessageData(v_goal_3156_, v_config_3157_, v___x_3166_, v___x_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3179_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3179_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3179_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 1);
lean_ctor_set(v___x_3170_, 0, v_mvarId_3155_);
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_mvarId_3155_);
v___x_3173_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3174_ = lean_obj_once(&l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1, &l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v_a_3168_);
v___x_3177_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(v___x_3176_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3177_;
}
}
}
else
{
lean_dec(v_mvarId_3155_);
return v___x_3167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed(lean_object* v_verbose_3180_, lean_object* v_mvarId_3181_, lean_object* v_goal_3182_, lean_object* v_config_3183_, lean_object* v___x_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v_verbose_boxed_3190_; uint8_t v___x_1179__boxed_3191_; lean_object* v_res_3192_; 
v_verbose_boxed_3190_ = lean_unbox(v_verbose_3180_);
v___x_1179__boxed_3191_ = lean_unbox(v___x_3184_);
v_res_3192_ = l_Lean_Meta_Grind_goalToMessageData___lam__0(v_verbose_boxed_3190_, v_mvarId_3181_, v_goal_3182_, v_config_3183_, v___x_1179__boxed_3191_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec_ref(v_goal_3182_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object* v_goal_3193_, lean_object* v_config_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
uint8_t v_verbose_3200_; lean_object* v_mvarId_3201_; uint8_t v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___y_3205_; lean_object* v___x_3206_; 
v_verbose_3200_ = lean_ctor_get_uint8(v_config_3194_, sizeof(void*)*13 + 15);
v_mvarId_3201_ = lean_ctor_get(v_goal_3193_, 1);
lean_inc_n(v_mvarId_3201_, 2);
v___x_3202_ = 1;
v___x_3203_ = lean_box(v_verbose_3200_);
v___x_3204_ = lean_box(v___x_3202_);
v___y_3205_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed), 10, 5);
lean_closure_set(v___y_3205_, 0, v___x_3203_);
lean_closure_set(v___y_3205_, 1, v_mvarId_3201_);
lean_closure_set(v___y_3205_, 2, v_goal_3193_);
lean_closure_set(v___y_3205_, 3, v_config_3194_);
lean_closure_set(v___y_3205_, 4, v___x_3204_);
v___x_3206_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3201_, v___y_3205_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___boxed(lean_object* v_goal_3207_, lean_object* v_config_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Meta_Grind_goalToMessageData(v_goal_3207_, v_config_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
return v_res_3214_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedResult_default = _init_l_Lean_Meta_Grind_instInhabitedResult_default();
l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult = _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Init_Grind_Injective(uint8_t builtin);
lean_object* initialize_Init_Grind_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_PP(builtin);
}
#ifdef __cplusplus
}
#endif
