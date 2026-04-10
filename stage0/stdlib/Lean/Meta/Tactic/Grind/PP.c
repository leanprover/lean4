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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Origin_pp(lean_object*);
lean_object* l_Lean_Meta_Grind_ppPattern(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_isTrue___boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grind_debug;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getTarget_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getEqcs(lean_object*, uint8_t);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFalse___boxed(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isCastLikeApp(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_Grind_isCastLikeDeclName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isTrue___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__0_value;
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFalse___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "False propositions"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prop"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(56, 247, 67, 203, 121, 106, 5, 21)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__4_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "True propositions"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_20_);
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
lean_dec_ref(v___x_22_);
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
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg(lean_object* v_e_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_st_ref_get(v_a_68_);
v___x_75_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v___x_74_, v_e_67_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
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
lean_dec_ref(v_goal_115_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v_b_119_);
return v___x_126_;
}
else
{
lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_127_ = lean_array_uget_borrowed(v_as_116_, v_i_118_);
lean_inc(v_a_127_);
lean_inc_ref(v_goal_115_);
v___x_128_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_115_, v_a_127_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; size_t v___x_133_; size_t v___x_134_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
lean_dec_ref(v___x_128_);
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
lean_dec_ref(v_goal_115_);
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
lean_dec_ref(v_x_150_);
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
lean_inc_ref(v_goal_149_);
v___x_174_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_149_, v_x_150_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref(v___x_174_);
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
lean_dec_ref(v_goal_149_);
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
lean_dec_ref(v___x_196_);
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
lean_dec_ref(v_goal_189_);
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
lean_dec_ref(v_goal_189_);
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
lean_dec_ref(v_goal_189_);
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
lean_dec_ref(v___x_248_);
if (lean_obj_tag(v_val_250_) == 1)
{
uint8_t v_v_251_; 
v_v_251_ = lean_ctor_get_uint8(v_val_250_, 0);
lean_dec_ref(v_val_250_);
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
lean_inc_ref(v_goal_276_);
v___x_308_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_276_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_308_);
lean_inc_ref(v_e_277_);
lean_inc_ref(v_goal_276_);
v___x_310_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(v_goal_276_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v___x_310_);
lean_inc_ref(v_e_277_);
lean_inc_ref(v_goal_276_);
v___x_312_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_276_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v_root_314_; uint8_t v_interpreted_315_; uint8_t v_ctor_316_; lean_object* v_r_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v_r_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v_root_314_ = lean_ctor_get(v_a_313_, 2);
lean_inc_ref(v_root_314_);
v_interpreted_315_ = lean_ctor_get_uint8(v_a_313_, sizeof(void*)*11 + 1);
v_ctor_316_ = lean_ctor_get_uint8(v_a_313_, sizeof(void*)*11 + 2);
lean_dec(v_a_313_);
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v_a_309_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_311_);
v___x_336_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_277_, v_root_314_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_inc_ref(v_goal_276_);
v___x_337_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_276_, v_root_314_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref(v___x_337_);
v___x_339_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_a_338_);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_335_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v_r_326_ = v___x_341_;
v___y_327_ = v_a_278_;
v___y_328_ = v_a_279_;
v___y_329_ = v_a_280_;
v___y_330_ = v_a_281_;
goto v___jp_325_;
}
else
{
lean_dec_ref(v___x_335_);
lean_dec_ref(v_e_277_);
lean_dec_ref(v_goal_276_);
return v___x_337_;
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
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_311_);
lean_dec(v_a_309_);
lean_dec_ref(v_e_277_);
lean_dec_ref(v_goal_276_);
v_a_342_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_312_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_312_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_dec(v_a_309_);
lean_dec_ref(v_e_277_);
lean_dec_ref(v_goal_276_);
return v___x_310_;
}
}
else
{
lean_dec_ref(v_e_277_);
lean_dec_ref(v_goal_276_);
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
lean_dec_ref(v_goal_276_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v_r_284_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; 
lean_inc_ref(v_goal_276_);
v___x_293_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v_goal_276_, v_e_277_);
lean_dec_ref(v_e_277_);
if (lean_obj_tag(v___x_293_) == 1)
{
lean_object* v_val_294_; lean_object* v___x_295_; 
v_val_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_val_294_);
lean_dec_ref(v___x_293_);
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
lean_dec_ref(v_goal_276_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v_r_284_);
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___boxed(lean_object* v_goal_350_, lean_object* v_e_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_350_, v_e_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(lean_object* v_goal_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec_ref(v_goal_358_);
v___x_366_ = l_List_reverse___redArg(v_x_360_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v_head_368_; lean_object* v_tail_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_387_; 
v_head_368_ = lean_ctor_get(v_x_359_, 0);
v_tail_369_ = lean_ctor_get(v_x_359_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_359_);
if (v_isSharedCheck_387_ == 0)
{
v___x_371_ = v_x_359_;
v_isShared_372_ = v_isSharedCheck_387_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_tail_369_);
lean_inc(v_head_368_);
lean_dec(v_x_359_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_387_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; 
lean_inc_ref(v_goal_358_);
v___x_373_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_358_, v_head_368_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v_x_360_);
lean_ctor_set(v___x_371_, 0, v_a_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_374_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_x_360_);
v___x_376_ = v_reuseFailAlloc_378_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v_x_359_ = v_tail_369_;
v_x_360_ = v___x_376_;
goto _start;
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_del_object(v___x_371_);
lean_dec(v_tail_369_);
lean_dec(v_x_360_);
lean_dec_ref(v_goal_358_);
v_a_379_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_373_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_373_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0___boxed(lean_object* v_goal_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(v_goal_388_, v_x_389_, v_x_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_396_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__1));
v___x_401_ = l_Lean_MessageData_ofFormat(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__4));
v___x_406_ = l_Lean_MessageData_ofFormat(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__7));
v___x_411_ = l_Lean_MessageData_ofFormat(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__10));
v___x_416_ = l_Lean_MessageData_ofFormat(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(lean_object* v_goal_417_, lean_object* v_as_x27_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
if (lean_obj_tag(v_as_x27_418_) == 0)
{
lean_object* v___x_425_; 
lean_dec_ref(v_goal_417_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v_b_419_);
return v___x_425_;
}
else
{
lean_object* v_head_426_; lean_object* v_tail_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_458_; 
v_head_426_ = lean_ctor_get(v_as_x27_418_, 0);
v_tail_427_ = lean_ctor_get(v_as_x27_418_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_as_x27_418_);
if (v_isSharedCheck_458_ == 0)
{
v___x_429_ = v_as_x27_418_;
v_isShared_430_ = v_isSharedCheck_458_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_tail_427_);
lean_inc(v_head_426_);
lean_dec(v_as_x27_418_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_458_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = l_List_lengthTR___redArg(v_head_426_);
v___x_433_ = lean_nat_dec_lt(v___x_431_, v___x_432_);
lean_dec(v___x_432_);
if (v___x_433_ == 0)
{
lean_del_object(v___x_429_);
lean_dec(v_head_426_);
v_as_x27_418_ = v_tail_427_;
goto _start;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_box(0);
lean_inc_ref(v_goal_417_);
v___x_436_ = l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(v_goal_417_, v_head_426_, v___x_435_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref(v___x_436_);
v___x_438_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 7);
lean_ctor_set(v___x_429_, 1, v___x_438_);
lean_ctor_set(v___x_429_, 0, v_b_419_);
v___x_440_ = v___x_429_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_b_419_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_449_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_441_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8);
v___x_444_ = l_Lean_MessageData_joinSep(v_a_437_, v___x_443_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_442_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v_as_x27_418_ = v_tail_427_;
v_b_419_ = v___x_447_;
goto _start;
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_del_object(v___x_429_);
lean_dec(v_tail_427_);
lean_dec_ref(v_b_419_);
lean_dec_ref(v_goal_417_);
v_a_450_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_436_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_436_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___boxed(lean_object* v_goal_459_, lean_object* v_as_x27_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_459_, v_as_x27_460_, v_b_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(lean_object* v_goal_468_, lean_object* v_as_469_, size_t v_sz_470_, size_t v_i_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_lt(v_i_471_, v_sz_470_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec_ref(v_goal_468_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_b_472_);
return v___x_479_;
}
else
{
lean_object* v_snd_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_516_; 
v_snd_480_ = lean_ctor_get(v_b_472_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_b_472_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_b_472_, 0);
lean_dec(v_unused_517_);
v___x_482_ = v_b_472_;
v_isShared_483_ = v_isSharedCheck_516_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snd_480_);
lean_dec(v_b_472_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_516_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_a_484_; lean_object* v___x_485_; 
v_a_484_ = lean_array_uget_borrowed(v_as_469_, v_i_471_);
lean_inc(v_a_484_);
lean_inc_ref(v_goal_468_);
v___x_485_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_468_, v_a_484_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v_self_487_; lean_object* v___x_488_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref(v___x_485_);
v_self_487_ = lean_ctor_get(v_a_486_, 0);
lean_inc_ref(v_self_487_);
lean_dec(v_a_486_);
lean_inc_ref(v_goal_468_);
v___x_488_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_468_, v_self_487_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v_snd_480_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v_a_489_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_493_);
lean_ctor_set(v___x_482_, 0, v___x_490_);
v___x_495_ = v___x_482_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
size_t v___x_496_; size_t v___x_497_; 
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_471_, v___x_496_);
v_i_471_ = v___x_497_;
v_b_472_ = v___x_495_;
goto _start;
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_del_object(v___x_482_);
lean_dec(v_snd_480_);
lean_dec_ref(v_goal_468_);
v_a_500_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_488_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_488_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_del_object(v___x_482_);
lean_dec(v_snd_480_);
lean_dec_ref(v_goal_468_);
v_a_508_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_485_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_485_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_goal_518_, lean_object* v_as_519_, lean_object* v_sz_520_, lean_object* v_i_521_, lean_object* v_b_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
size_t v_sz_boxed_528_; size_t v_i_boxed_529_; lean_object* v_res_530_; 
v_sz_boxed_528_ = lean_unbox_usize(v_sz_520_);
lean_dec(v_sz_520_);
v_i_boxed_529_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(v_goal_518_, v_as_519_, v_sz_boxed_528_, v_i_boxed_529_, v_b_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v_as_519_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(lean_object* v_goal_531_, lean_object* v_as_532_, size_t v_sz_533_, size_t v_i_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_lt(v_i_534_, v_sz_533_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
lean_dec_ref(v_goal_531_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v_b_535_);
return v___x_542_;
}
else
{
lean_object* v_snd_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_579_; 
v_snd_543_ = lean_ctor_get(v_b_535_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_b_535_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v_b_535_, 0);
lean_dec(v_unused_580_);
v___x_545_ = v_b_535_;
v_isShared_546_ = v_isSharedCheck_579_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_snd_543_);
lean_dec(v_b_535_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_579_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_a_547_; lean_object* v___x_548_; 
v_a_547_ = lean_array_uget_borrowed(v_as_532_, v_i_534_);
lean_inc(v_a_547_);
lean_inc_ref(v_goal_531_);
v___x_548_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_531_, v_a_547_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v_self_550_; lean_object* v___x_551_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_548_);
v_self_550_ = lean_ctor_get(v_a_549_, 0);
lean_inc_ref(v_self_550_);
lean_dec(v_a_549_);
lean_inc_ref(v_goal_531_);
v___x_551_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_531_, v_self_550_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref(v___x_551_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v_snd_543_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v_a_552_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_556_);
lean_ctor_set(v___x_545_, 0, v___x_553_);
v___x_558_ = v___x_545_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_556_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_534_, v___x_559_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(v_goal_531_, v_as_532_, v_sz_533_, v___x_560_, v___x_558_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
return v___x_561_;
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_545_);
lean_dec(v_snd_543_);
lean_dec_ref(v_goal_531_);
v_a_563_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_551_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_551_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_545_);
lean_dec(v_snd_543_);
lean_dec_ref(v_goal_531_);
v_a_571_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_548_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_548_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3___boxed(lean_object* v_goal_581_, lean_object* v_as_582_, lean_object* v_sz_583_, lean_object* v_i_584_, lean_object* v_b_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
size_t v_sz_boxed_591_; size_t v_i_boxed_592_; lean_object* v_res_593_; 
v_sz_boxed_591_ = lean_unbox_usize(v_sz_583_);
lean_dec(v_sz_583_);
v_i_boxed_592_ = lean_unbox_usize(v_i_584_);
lean_dec(v_i_584_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(v_goal_581_, v_as_582_, v_sz_boxed_591_, v_i_boxed_592_, v_b_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec_ref(v_as_582_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(lean_object* v_init_594_, lean_object* v_goal_595_, lean_object* v_n_596_, lean_object* v_b_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
if (lean_obj_tag(v_n_596_) == 0)
{
lean_object* v_cs_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_637_; 
v_cs_603_ = lean_ctor_get(v_n_596_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v_n_596_);
if (v_isSharedCheck_637_ == 0)
{
v___x_605_ = v_n_596_;
v_isShared_606_ = v_isSharedCheck_637_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_cs_603_);
lean_dec(v_n_596_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_637_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; size_t v_sz_609_; size_t v___x_610_; lean_object* v___x_611_; 
v___x_607_ = lean_box(0);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_b_597_);
v_sz_609_ = lean_array_size(v_cs_603_);
v___x_610_ = ((size_t)0ULL);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(v_init_594_, v_goal_595_, v_cs_603_, v_sz_609_, v___x_610_, v___x_608_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec_ref(v_cs_603_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_628_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_628_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_628_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_628_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_fst_616_; 
v_fst_616_ = lean_ctor_get(v_a_612_, 0);
if (lean_obj_tag(v_fst_616_) == 0)
{
lean_object* v_snd_617_; lean_object* v___x_619_; 
v_snd_617_ = lean_ctor_get(v_a_612_, 1);
lean_inc(v_snd_617_);
lean_dec(v_a_612_);
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 1);
lean_ctor_set(v___x_605_, 0, v_snd_617_);
v___x_619_ = v___x_605_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_snd_617_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_619_);
v___x_621_ = v___x_614_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v_val_624_; lean_object* v___x_626_; 
lean_inc_ref(v_fst_616_);
lean_dec(v_a_612_);
lean_del_object(v___x_605_);
v_val_624_ = lean_ctor_get(v_fst_616_, 0);
lean_inc(v_val_624_);
lean_dec_ref(v_fst_616_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v_val_624_);
v___x_626_ = v___x_614_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_val_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_del_object(v___x_605_);
v_a_629_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_611_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_611_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
else
{
lean_object* v_vs_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_672_; 
v_vs_638_ = lean_ctor_get(v_n_596_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_n_596_);
if (v_isSharedCheck_672_ == 0)
{
v___x_640_ = v_n_596_;
v_isShared_641_ = v_isSharedCheck_672_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_vs_638_);
lean_dec(v_n_596_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_672_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; size_t v_sz_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_b_597_);
v_sz_644_ = lean_array_size(v_vs_638_);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(v_goal_595_, v_vs_638_, v_sz_644_, v___x_645_, v___x_643_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec_ref(v_vs_638_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_663_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_663_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_663_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_663_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_fst_651_; 
v_fst_651_ = lean_ctor_get(v_a_647_, 0);
if (lean_obj_tag(v_fst_651_) == 0)
{
lean_object* v_snd_652_; lean_object* v___x_654_; 
v_snd_652_ = lean_ctor_get(v_a_647_, 1);
lean_inc(v_snd_652_);
lean_dec(v_a_647_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_snd_652_);
v___x_654_ = v___x_640_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_snd_652_);
v___x_654_ = v_reuseFailAlloc_658_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_656_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_654_);
v___x_656_ = v___x_649_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
else
{
lean_object* v_val_659_; lean_object* v___x_661_; 
lean_inc_ref(v_fst_651_);
lean_dec(v_a_647_);
lean_del_object(v___x_640_);
v_val_659_ = lean_ctor_get(v_fst_651_, 0);
lean_inc(v_val_659_);
lean_dec_ref(v_fst_651_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v_val_659_);
v___x_661_ = v___x_649_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_val_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_del_object(v___x_640_);
v_a_664_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_646_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_646_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(lean_object* v_init_673_, lean_object* v_goal_674_, lean_object* v_as_675_, size_t v_sz_676_, size_t v_i_677_, lean_object* v_b_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_lt(v_i_677_, v_sz_676_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec_ref(v_goal_674_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_678_);
return v___x_685_;
}
else
{
lean_object* v_snd_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_720_; 
v_snd_686_ = lean_ctor_get(v_b_678_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_b_678_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_b_678_, 0);
lean_dec(v_unused_721_);
v___x_688_ = v_b_678_;
v_isShared_689_ = v_isSharedCheck_720_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_snd_686_);
lean_dec(v_b_678_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_720_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_a_690_; lean_object* v___x_691_; 
v_a_690_ = lean_array_uget_borrowed(v_as_675_, v_i_677_);
lean_inc(v_snd_686_);
lean_inc(v_a_690_);
lean_inc_ref(v_goal_674_);
v___x_691_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_673_, v_goal_674_, v_a_690_, v_snd_686_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_711_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_711_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_711_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_711_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
if (lean_obj_tag(v_a_692_) == 0)
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec_ref(v_goal_674_);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_a_692_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_696_);
v___x_698_ = v___x_688_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_snd_686_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_698_);
v___x_700_ = v___x_694_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
lean_del_object(v___x_694_);
lean_dec(v_snd_686_);
v_a_703_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v_a_692_);
v___x_704_ = lean_box(0);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_a_703_);
lean_ctor_set(v___x_688_, 0, v___x_704_);
v___x_706_ = v___x_688_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_a_703_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
size_t v___x_707_; size_t v___x_708_; 
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_677_, v___x_707_);
v_i_677_ = v___x_708_;
v_b_678_ = v___x_706_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_del_object(v___x_688_);
lean_dec(v_snd_686_);
lean_dec_ref(v_goal_674_);
v_a_712_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_691_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_691_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2___boxed(lean_object* v_init_722_, lean_object* v_goal_723_, lean_object* v_as_724_, lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
size_t v_sz_boxed_733_; size_t v_i_boxed_734_; lean_object* v_res_735_; 
v_sz_boxed_733_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_734_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(v_init_722_, v_goal_723_, v_as_724_, v_sz_boxed_733_, v_i_boxed_734_, v_b_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec_ref(v_as_724_);
lean_dec_ref(v_init_722_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1___boxed(lean_object* v_init_736_, lean_object* v_goal_737_, lean_object* v_n_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_736_, v_goal_737_, v_n_738_, v_b_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec_ref(v_init_736_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(lean_object* v_goal_746_, lean_object* v_as_747_, size_t v_sz_748_, size_t v_i_749_, lean_object* v_b_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_lt(v_i_749_, v_sz_748_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec_ref(v_goal_746_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_b_750_);
return v___x_757_;
}
else
{
lean_object* v_snd_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_794_; 
v_snd_758_ = lean_ctor_get(v_b_750_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_b_750_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_b_750_, 0);
lean_dec(v_unused_795_);
v___x_760_ = v_b_750_;
v_isShared_761_ = v_isSharedCheck_794_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_758_);
lean_dec(v_b_750_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_794_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_array_uget_borrowed(v_as_747_, v_i_749_);
lean_inc(v_a_762_);
lean_inc_ref(v_goal_746_);
v___x_763_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_746_, v_a_762_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v_self_765_; lean_object* v___x_766_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref(v___x_763_);
v_self_765_ = lean_ctor_get(v_a_764_, 0);
lean_inc_ref(v_self_765_);
lean_dec(v_a_764_);
lean_inc_ref(v_goal_746_);
v___x_766_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_746_, v_self_765_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
v___x_768_ = lean_box(0);
v___x_769_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v_snd_758_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v_a_767_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_771_);
lean_ctor_set(v___x_760_, 0, v___x_768_);
v___x_773_ = v___x_760_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
size_t v___x_774_; size_t v___x_775_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_749_, v___x_774_);
v_i_749_ = v___x_775_;
v_b_750_ = v___x_773_;
goto _start;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_760_);
lean_dec(v_snd_758_);
lean_dec_ref(v_goal_746_);
v_a_778_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_766_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_766_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_del_object(v___x_760_);
lean_dec(v_snd_758_);
lean_dec_ref(v_goal_746_);
v_a_786_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_763_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_763_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5___boxed(lean_object* v_goal_796_, lean_object* v_as_797_, lean_object* v_sz_798_, lean_object* v_i_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
size_t v_sz_boxed_806_; size_t v_i_boxed_807_; lean_object* v_res_808_; 
v_sz_boxed_806_ = lean_unbox_usize(v_sz_798_);
lean_dec(v_sz_798_);
v_i_boxed_807_ = lean_unbox_usize(v_i_799_);
lean_dec(v_i_799_);
v_res_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(v_goal_796_, v_as_797_, v_sz_boxed_806_, v_i_boxed_807_, v_b_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_as_797_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(lean_object* v_goal_809_, lean_object* v_as_810_, size_t v_sz_811_, size_t v_i_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_lt(v_i_812_, v_sz_811_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_dec_ref(v_goal_809_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_b_813_);
return v___x_820_;
}
else
{
lean_object* v_snd_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_857_; 
v_snd_821_ = lean_ctor_get(v_b_813_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_b_813_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; 
v_unused_858_ = lean_ctor_get(v_b_813_, 0);
lean_dec(v_unused_858_);
v___x_823_ = v_b_813_;
v_isShared_824_ = v_isSharedCheck_857_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_821_);
lean_dec(v_b_813_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_857_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_a_825_; lean_object* v___x_826_; 
v_a_825_ = lean_array_uget_borrowed(v_as_810_, v_i_812_);
lean_inc(v_a_825_);
lean_inc_ref(v_goal_809_);
v___x_826_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_809_, v_a_825_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v_self_828_; lean_object* v___x_829_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_826_);
v_self_828_ = lean_ctor_get(v_a_827_, 0);
lean_inc_ref(v_self_828_);
lean_dec(v_a_827_);
lean_inc_ref(v_goal_809_);
v___x_829_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_809_, v_self_828_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref(v___x_829_);
v___x_831_ = lean_box(0);
v___x_832_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v_snd_821_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v_a_830_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_834_);
lean_ctor_set(v___x_823_, 0, v___x_831_);
v___x_836_ = v___x_823_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_834_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_812_, v___x_837_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(v_goal_809_, v_as_810_, v_sz_811_, v___x_838_, v___x_836_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_839_;
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_del_object(v___x_823_);
lean_dec(v_snd_821_);
lean_dec_ref(v_goal_809_);
v_a_841_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_829_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_829_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_del_object(v___x_823_);
lean_dec(v_snd_821_);
lean_dec_ref(v_goal_809_);
v_a_849_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_826_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_826_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2___boxed(lean_object* v_goal_859_, lean_object* v_as_860_, lean_object* v_sz_861_, lean_object* v_i_862_, lean_object* v_b_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
size_t v_sz_boxed_869_; size_t v_i_boxed_870_; lean_object* v_res_871_; 
v_sz_boxed_869_ = lean_unbox_usize(v_sz_861_);
lean_dec(v_sz_861_);
v_i_boxed_870_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_res_871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(v_goal_859_, v_as_860_, v_sz_boxed_869_, v_i_boxed_870_, v_b_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v_as_860_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(lean_object* v_goal_872_, lean_object* v_t_873_, lean_object* v_init_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_root_880_; lean_object* v_tail_881_; lean_object* v___x_882_; 
v_root_880_ = lean_ctor_get(v_t_873_, 0);
lean_inc_ref(v_root_880_);
v_tail_881_ = lean_ctor_get(v_t_873_, 1);
lean_inc_ref(v_tail_881_);
lean_dec_ref(v_t_873_);
lean_inc_ref(v_goal_872_);
lean_inc_ref(v_init_874_);
v___x_882_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_874_, v_goal_872_, v_root_880_, v_init_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec_ref(v_init_874_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_919_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_919_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_919_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_919_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
if (lean_obj_tag(v_a_883_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; 
lean_dec_ref(v_tail_881_);
lean_dec_ref(v_goal_872_);
v_a_887_ = lean_ctor_get(v_a_883_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v_a_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_a_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; size_t v_sz_894_; size_t v___x_895_; lean_object* v___x_896_; 
lean_del_object(v___x_885_);
v_a_891_ = lean_ctor_get(v_a_883_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v_a_883_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v_a_891_);
v_sz_894_ = lean_array_size(v_tail_881_);
v___x_895_ = ((size_t)0ULL);
v___x_896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(v_goal_872_, v_tail_881_, v_sz_894_, v___x_895_, v___x_893_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec_ref(v_tail_881_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_910_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_910_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_910_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_910_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_fst_901_; 
v_fst_901_ = lean_ctor_get(v_a_897_, 0);
if (lean_obj_tag(v_fst_901_) == 0)
{
lean_object* v_snd_902_; lean_object* v___x_904_; 
v_snd_902_ = lean_ctor_get(v_a_897_, 1);
lean_inc(v_snd_902_);
lean_dec(v_a_897_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v_snd_902_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_snd_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
else
{
lean_object* v_val_906_; lean_object* v___x_908_; 
lean_inc_ref(v_fst_901_);
lean_dec(v_a_897_);
v_val_906_ = lean_ctor_get(v_fst_901_, 0);
lean_inc(v_val_906_);
lean_dec_ref(v_fst_901_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v_val_906_);
v___x_908_ = v___x_899_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_val_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_896_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_896_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v_tail_881_);
lean_dec_ref(v_goal_872_);
v_a_920_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_882_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_882_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1___boxed(lean_object* v_goal_928_, lean_object* v_t_929_, lean_object* v_init_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(v_goal_928_, v_t_929_, v_init_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
return v_res_936_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Goal_ppState___closed__1(void){
_start:
{
lean_object* v___x_938_; lean_object* v_r_939_; 
v___x_938_ = ((lean_object*)(l_Lean_Meta_Grind_Goal_ppState___closed__0));
v_r_939_ = l_Lean_stringToMessageData(v___x_938_);
return v_r_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object* v_goal_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_toGoalState_946_; lean_object* v_exprs_947_; lean_object* v_r_948_; lean_object* v___x_949_; 
v_toGoalState_946_ = lean_ctor_get(v_goal_940_, 0);
v_exprs_947_ = lean_ctor_get(v_toGoalState_946_, 2);
v_r_948_ = lean_obj_once(&l_Lean_Meta_Grind_Goal_ppState___closed__1, &l_Lean_Meta_Grind_Goal_ppState___closed__1_once, _init_l_Lean_Meta_Grind_Goal_ppState___closed__1);
lean_inc_ref(v_exprs_947_);
lean_inc_ref(v_goal_940_);
v___x_949_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(v_goal_940_, v_exprs_947_, v_r_948_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref(v___x_949_);
v___x_951_ = 1;
lean_inc_ref(v_goal_940_);
v___x_952_ = l_Lean_Meta_Grind_Goal_getEqcs(v_goal_940_, v___x_951_);
v___x_953_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_940_, v___x_952_, v_a_950_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_953_;
}
else
{
lean_dec_ref(v_goal_940_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppState___boxed(lean_object* v_goal_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_Grind_Goal_ppState(v_goal_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(lean_object* v_goal_961_, lean_object* v_as_962_, lean_object* v_as_x27_963_, lean_object* v_b_964_, lean_object* v_a_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_961_, v_as_x27_963_, v_b_964_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___boxed(lean_object* v_goal_972_, lean_object* v_as_973_, lean_object* v_as_x27_974_, lean_object* v_b_975_, lean_object* v_a_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(v_goal_972_, v_as_973_, v_as_x27_974_, v_b_975_, v_a_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v_as_973_);
return v_res_982_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_box(1);
v___x_984_ = l_Lean_MessageData_ofFormat(v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(lean_object* v_as_x27_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
if (lean_obj_tag(v_as_x27_985_) == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_986_);
return v___x_992_;
}
else
{
lean_object* v_head_993_; lean_object* v_tail_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1006_; 
v_head_993_ = lean_ctor_get(v_as_x27_985_, 0);
v_tail_994_ = lean_ctor_get(v_as_x27_985_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_as_x27_985_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_996_ = v_as_x27_985_;
v_isShared_997_ = v_isSharedCheck_1006_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_tail_994_);
lean_inc(v_head_993_);
lean_dec(v_as_x27_985_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1006_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Grind_Goal_ppState(v_head_993_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v___x_998_);
v___x_1000_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 7);
lean_ctor_set(v___x_996_, 1, v___x_1000_);
lean_ctor_set(v___x_996_, 0, v_b_986_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_b_986_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v_a_999_);
v_as_x27_985_ = v_tail_994_;
v_b_986_ = v___x_1003_;
goto _start;
}
}
else
{
lean_del_object(v___x_996_);
lean_dec(v_tail_994_);
lean_dec_ref(v_b_986_);
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___boxed(lean_object* v_as_x27_1007_, lean_object* v_b_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_as_x27_1007_, v_b_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1014_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_1016_; lean_object* v_r_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v_r_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppGoals(lean_object* v_goals_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_r_1024_; lean_object* v___x_1025_; 
v_r_1024_ = lean_obj_once(&l_Lean_Meta_Grind_ppGoals___closed__1, &l_Lean_Meta_Grind_ppGoals___closed__1_once, _init_l_Lean_Meta_Grind_ppGoals___closed__1);
v___x_1025_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_goals_1018_, v_r_1024_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppGoals___boxed(lean_object* v_goals_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Meta_Grind_ppGoals(v_goals_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(lean_object* v_as_1033_, lean_object* v_as_x27_1034_, lean_object* v_b_1035_, lean_object* v_a_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_as_x27_1034_, v_b_1035_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___boxed(lean_object* v_as_1043_, lean_object* v_as_x27_1044_, lean_object* v_b_1045_, lean_object* v_a_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(v_as_1043_, v_as_x27_1044_, v_b_1045_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v_as_1043_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(lean_object* v_m_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_array_push(v_a_1054_, v_m_1053_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg___boxed(lean_object* v_m_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_m_1060_, v_a_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(lean_object* v_m_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_m_1064_, v_a_1066_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___boxed(lean_object* v_m_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(v_m_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec_ref(v_a_1074_);
return v_res_1081_;
}
}
static double _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1082_; double v___x_1083_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_float_of_nat(v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(lean_object* v_e_1086_, lean_object* v_cls_1087_){
_start:
{
lean_object* v___x_1088_; double v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1090_ = 1;
v___x_1091_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1092_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1092_, 0, v_cls_1087_);
lean_ctor_set(v___x_1092_, 1, v___x_1088_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
lean_ctor_set_float(v___x_1092_, sizeof(void*)*3, v___x_1089_);
lean_ctor_set_float(v___x_1092_, sizeof(void*)*3 + 8, v___x_1089_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*3 + 16, v___x_1090_);
v___x_1093_ = l_Lean_MessageData_ofExpr(v_e_1086_);
v___x_1094_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1095_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1092_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
lean_ctor_set(v___x_1095_, 2, v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(lean_object* v_clsElem_1096_, size_t v_sz_1097_, size_t v_i_1098_, lean_object* v_bs_1099_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_usize_dec_lt(v_i_1098_, v_sz_1097_);
if (v___x_1100_ == 0)
{
lean_dec(v_clsElem_1096_);
return v_bs_1099_;
}
else
{
lean_object* v_v_1101_; lean_object* v___x_1102_; lean_object* v_bs_x27_1103_; lean_object* v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; 
v_v_1101_ = lean_array_uget(v_bs_1099_, v_i_1098_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v_bs_x27_1103_ = lean_array_uset(v_bs_1099_, v_i_1098_, v___x_1102_);
lean_inc(v_clsElem_1096_);
v___x_1104_ = l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(v_v_1101_, v_clsElem_1096_);
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_add(v_i_1098_, v___x_1105_);
v___x_1107_ = lean_array_uset(v_bs_x27_1103_, v_i_1098_, v___x_1104_);
v_i_1098_ = v___x_1106_;
v_bs_1099_ = v___x_1107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1___boxed(lean_object* v_clsElem_1109_, lean_object* v_sz_1110_, lean_object* v_i_1111_, lean_object* v_bs_1112_){
_start:
{
size_t v_sz_boxed_1113_; size_t v_i_boxed_1114_; lean_object* v_res_1115_; 
v_sz_boxed_1113_ = lean_unbox_usize(v_sz_1110_);
lean_dec(v_sz_1110_);
v_i_boxed_1114_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_res_1115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(v_clsElem_1109_, v_sz_boxed_1113_, v_i_boxed_1114_, v_bs_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppExprArray(lean_object* v_cls_1116_, lean_object* v_header_1117_, lean_object* v_es_1118_, lean_object* v_clsElem_1119_, uint8_t v_collapsed_1120_){
_start:
{
size_t v_sz_1121_; size_t v___x_1122_; lean_object* v_es_1123_; lean_object* v___x_1124_; double v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_sz_1121_ = lean_array_size(v_es_1118_);
v___x_1122_ = ((size_t)0ULL);
v_es_1123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(v_clsElem_1119_, v_sz_1121_, v___x_1122_, v_es_1118_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1126_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1127_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1127_, 0, v_cls_1116_);
lean_ctor_set(v___x_1127_, 1, v___x_1124_);
lean_ctor_set(v___x_1127_, 2, v___x_1126_);
lean_ctor_set_float(v___x_1127_, sizeof(void*)*3, v___x_1125_);
lean_ctor_set_float(v___x_1127_, sizeof(void*)*3 + 8, v___x_1125_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*3 + 16, v_collapsed_1120_);
v___x_1128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_header_1117_);
v___x_1129_ = l_Lean_MessageData_ofFormat(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1127_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
lean_ctor_set(v___x_1130_, 2, v_es_1123_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppExprArray___boxed(lean_object* v_cls_1131_, lean_object* v_header_1132_, lean_object* v_es_1133_, lean_object* v_clsElem_1134_, lean_object* v_collapsed_1135_){
_start:
{
uint8_t v_collapsed_boxed_1136_; lean_object* v_res_1137_; 
v_collapsed_boxed_1136_ = lean_unbox(v_collapsed_1135_);
v_res_1137_ = l_Lean_Meta_Grind_ppExprArray(v_cls_1131_, v_header_1132_, v_es_1133_, v_clsElem_1134_, v_collapsed_boxed_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(lean_object* v_declName_1148_){
_start:
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1));
v___x_1150_ = lean_name_eq(v_declName_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3));
v___x_1152_ = lean_name_eq(v_declName_1148_, v___x_1151_);
return v___x_1152_;
}
else
{
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___boxed(lean_object* v_declName_1153_){
_start:
{
uint8_t v_res_1154_; lean_object* v_r_1155_; 
v_res_1154_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(v_declName_1153_);
lean_dec(v_declName_1153_);
v_r_1155_ = lean_box(v_res_1154_);
return v_r_1155_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(lean_object* v_declName_1165_){
_start:
{
uint8_t v___y_1167_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3));
v___x_1171_ = lean_name_eq(v_declName_1165_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5));
v___x_1173_ = lean_name_eq(v_declName_1165_, v___x_1172_);
v___y_1167_ = v___x_1173_;
goto v___jp_1166_;
}
else
{
v___y_1167_ = v___x_1171_;
goto v___jp_1166_;
}
v___jp_1166_:
{
if (v___y_1167_ == 0)
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1));
v___x_1169_ = lean_name_eq(v_declName_1165_, v___x_1168_);
return v___x_1169_;
}
else
{
return v___y_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___boxed(lean_object* v_declName_1174_){
_start:
{
uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_res_1175_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_1174_);
lean_dec(v_declName_1174_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(uint8_t v_x_1177_){
_start:
{
switch(v_x_1177_)
{
case 0:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_unsigned_to_nat(0u);
return v___x_1178_;
}
case 1:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_unsigned_to_nat(1u);
return v___x_1179_;
}
default: 
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_unsigned_to_nat(2u);
return v___x_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___boxed(lean_object* v_x_1181_){
_start:
{
uint8_t v_x_boxed_1182_; lean_object* v_res_1183_; 
v_x_boxed_1182_ = lean_unbox(v_x_1181_);
v_res_1183_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(v_x_boxed_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(uint8_t v_x_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(v_x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx___boxed(lean_object* v_x_1186_){
_start:
{
uint8_t v_x_4__boxed_1187_; lean_object* v_res_1188_; 
v_x_4__boxed_1187_ = lean_unbox(v_x_1186_);
v_res_1188_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(v_x_4__boxed_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(lean_object* v_k_1189_){
_start:
{
lean_inc(v_k_1189_);
return v_k_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg___boxed(lean_object* v_k_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(v_k_1190_);
lean_dec(v_k_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(lean_object* v_motive_1192_, lean_object* v_ctorIdx_1193_, uint8_t v_t_1194_, lean_object* v_h_1195_, lean_object* v_k_1196_){
_start:
{
lean_inc(v_k_1196_);
return v_k_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___boxed(lean_object* v_motive_1197_, lean_object* v_ctorIdx_1198_, lean_object* v_t_1199_, lean_object* v_h_1200_, lean_object* v_k_1201_){
_start:
{
uint8_t v_t_boxed_1202_; lean_object* v_res_1203_; 
v_t_boxed_1202_ = lean_unbox(v_t_1199_);
v_res_1203_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(v_motive_1197_, v_ctorIdx_1198_, v_t_boxed_1202_, v_h_1200_, v_k_1201_);
lean_dec(v_k_1201_);
lean_dec(v_ctorIdx_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(lean_object* v_num_1204_){
_start:
{
lean_inc(v_num_1204_);
return v_num_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg___boxed(lean_object* v_num_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(v_num_1205_);
lean_dec(v_num_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(lean_object* v_motive_1207_, uint8_t v_t_1208_, lean_object* v_h_1209_, lean_object* v_num_1210_){
_start:
{
lean_inc(v_num_1210_);
return v_num_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___boxed(lean_object* v_motive_1211_, lean_object* v_t_1212_, lean_object* v_h_1213_, lean_object* v_num_1214_){
_start:
{
uint8_t v_t_boxed_1215_; lean_object* v_res_1216_; 
v_t_boxed_1215_ = lean_unbox(v_t_1212_);
v_res_1216_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(v_motive_1211_, v_t_boxed_1215_, v_h_1213_, v_num_1214_);
lean_dec(v_num_1214_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(lean_object* v_cast_1217_){
_start:
{
lean_inc(v_cast_1217_);
return v_cast_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg___boxed(lean_object* v_cast_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(v_cast_1218_);
lean_dec(v_cast_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(lean_object* v_motive_1220_, uint8_t v_t_1221_, lean_object* v_h_1222_, lean_object* v_cast_1223_){
_start:
{
lean_inc(v_cast_1223_);
return v_cast_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___boxed(lean_object* v_motive_1224_, lean_object* v_t_1225_, lean_object* v_h_1226_, lean_object* v_cast_1227_){
_start:
{
uint8_t v_t_boxed_1228_; lean_object* v_res_1229_; 
v_t_boxed_1228_ = lean_unbox(v_t_1225_);
v_res_1229_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(v_motive_1224_, v_t_boxed_1228_, v_h_1226_, v_cast_1227_);
lean_dec(v_cast_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(lean_object* v_no_1230_){
_start:
{
lean_inc(v_no_1230_);
return v_no_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg___boxed(lean_object* v_no_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(v_no_1231_);
lean_dec(v_no_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(lean_object* v_motive_1233_, uint8_t v_t_1234_, lean_object* v_h_1235_, lean_object* v_no_1236_){
_start:
{
lean_inc(v_no_1236_);
return v_no_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___boxed(lean_object* v_motive_1237_, lean_object* v_t_1238_, lean_object* v_h_1239_, lean_object* v_no_1240_){
_start:
{
uint8_t v_t_boxed_1241_; lean_object* v_res_1242_; 
v_t_boxed_1241_ = lean_unbox(v_t_1238_);
v_res_1242_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(v_motive_1237_, v_t_boxed_1241_, v_h_1239_, v_no_1240_);
lean_dec(v_no_1240_);
return v_res_1242_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedResult_default(void){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = 0;
return v___x_1243_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult(void){
_start:
{
uint8_t v___x_1244_; 
v___x_1244_ = 0;
return v___x_1244_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(lean_object* v_e_1285_){
_start:
{
lean_object* v_a_1291_; lean_object* v_b_1292_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
lean_inc_ref(v_e_1285_);
v___x_1296_ = l_Lean_Expr_cleanupAnnotations(v_e_1285_);
v___x_1297_ = l_Lean_Expr_isApp(v___x_1296_);
if (v___x_1297_ == 0)
{
lean_dec_ref(v___x_1296_);
goto v___jp_1286_;
}
else
{
lean_object* v_arg_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v_arg_1298_ = lean_ctor_get(v___x_1296_, 1);
lean_inc_ref(v_arg_1298_);
v___x_1299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1296_);
v___x_1300_ = l_Lean_Expr_isApp(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_dec_ref(v___x_1299_);
lean_dec_ref(v_arg_1298_);
goto v___jp_1286_;
}
else
{
lean_object* v_arg_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_arg_1301_ = lean_ctor_get(v___x_1299_, 1);
lean_inc_ref(v_arg_1301_);
v___x_1302_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1299_);
v___x_1303_ = l_Lean_Expr_isApp(v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec_ref(v___x_1302_);
lean_dec_ref(v_arg_1301_);
lean_dec_ref(v_arg_1298_);
goto v___jp_1286_;
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1302_);
v___x_1305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2));
v___x_1306_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5));
v___x_1308_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1307_);
if (v___x_1308_ == 0)
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Lean_Expr_isApp(v___x_1304_);
if (v___x_1309_ == 0)
{
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1301_);
lean_dec_ref(v_arg_1298_);
goto v___jp_1286_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1304_);
v___x_1311_ = l_Lean_Expr_isApp(v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec_ref(v___x_1310_);
lean_dec_ref(v_arg_1301_);
lean_dec_ref(v_arg_1298_);
goto v___jp_1286_;
}
else
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1310_);
v___x_1313_ = l_Lean_Expr_isApp(v___x_1312_);
if (v___x_1313_ == 0)
{
lean_dec_ref(v___x_1312_);
lean_dec_ref(v_arg_1301_);
lean_dec_ref(v_arg_1298_);
goto v___jp_1286_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1312_);
v___x_1315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8));
v___x_1316_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11));
v___x_1318_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14));
v___x_1320_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17));
v___x_1322_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20));
v___x_1324_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23));
v___x_1326_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1325_);
lean_dec_ref(v___x_1314_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v_arg_1301_);
lean_dec_ref(v_arg_1298_);
goto v___jp_1286_;
}
else
{
lean_dec_ref(v_e_1285_);
v_a_1291_ = v_arg_1301_;
v_b_1292_ = v_arg_1298_;
goto v___jp_1290_;
}
}
else
{
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_e_1285_);
v_a_1291_ = v_arg_1301_;
v_b_1292_ = v_arg_1298_;
goto v___jp_1290_;
}
}
else
{
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_e_1285_);
v_a_1291_ = v_arg_1301_;
v_b_1292_ = v_arg_1298_;
goto v___jp_1290_;
}
}
else
{
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_e_1285_);
v_a_1291_ = v_arg_1301_;
v_b_1292_ = v_arg_1298_;
goto v___jp_1290_;
}
}
else
{
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_e_1285_);
v_a_1291_ = v_arg_1301_;
v_b_1292_ = v_arg_1298_;
goto v___jp_1290_;
}
}
else
{
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_arg_1298_);
lean_dec_ref(v_e_1285_);
v_e_1285_ = v_arg_1301_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1301_);
lean_dec_ref(v_e_1285_);
v_e_1285_ = v_arg_1298_;
goto _start;
}
}
else
{
uint8_t v___x_1329_; 
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1301_);
lean_dec_ref(v_arg_1298_);
lean_dec_ref(v_e_1285_);
v___x_1329_ = 0;
return v___x_1329_;
}
}
}
}
v___jp_1286_:
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_Meta_Grind_isCastLikeApp(v_e_1285_);
lean_dec_ref(v_e_1285_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; 
v___x_1288_ = 2;
return v___x_1288_;
}
else
{
uint8_t v___x_1289_; 
v___x_1289_ = 1;
return v___x_1289_;
}
}
v___jp_1290_:
{
uint8_t v___x_1293_; 
v___x_1293_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_a_1291_);
switch(v___x_1293_)
{
case 0:
{
uint8_t v___x_1294_; 
v___x_1294_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_1292_);
if (v___x_1294_ == 0)
{
return v___x_1294_;
}
else
{
return v___x_1294_;
}
}
case 1:
{
uint8_t v___x_1295_; 
v___x_1295_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_1292_);
switch(v___x_1295_)
{
case 2:
{
return v___x_1295_;
}
case 1:
{
return v___x_1295_;
}
default: 
{
return v___x_1293_;
}
}
}
default: 
{
lean_dec_ref(v_b_1292_);
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___boxed(lean_object* v_e_1330_){
_start:
{
uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_res_1331_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_1330_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(lean_object* v_e_1333_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_1333_);
if (v___x_1334_ == 1)
{
uint8_t v___x_1335_; 
v___x_1335_ = 1;
return v___x_1335_;
}
else
{
uint8_t v___x_1336_; 
v___x_1336_ = 0;
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike___boxed(lean_object* v_e_1337_){
_start:
{
uint8_t v_res_1338_; lean_object* v_r_1339_; 
v_res_1338_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_1337_);
v_r_1339_ = lean_box(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(lean_object* v_declName_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v_env_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1343_ = lean_st_ref_get(v___y_1341_);
v_env_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc_ref(v_env_1344_);
lean_dec(v___x_1343_);
v___x_1345_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1344_, v_declName_1340_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg___boxed(lean_object* v_declName_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1347_, v___y_1348_);
lean_dec(v___y_1348_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(lean_object* v_declName_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1351_, v___y_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___boxed(lean_object* v_declName_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(v_declName_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp(lean_object* v_e_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
uint8_t v___x_1371_; uint8_t v___x_1372_; 
lean_inc_ref(v_e_1365_);
v___x_1371_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_1365_);
v___x_1372_ = 1;
if (v___x_1371_ == 0)
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Expr_getAppFn(v_e_1365_);
if (lean_obj_tag(v___x_1373_) == 4)
{
lean_object* v_declName_1374_; lean_object* v___y_1376_; lean_object* v___x_1391_; lean_object* v_a_1392_; 
v_declName_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc_n(v_declName_1374_, 2);
lean_dec_ref(v___x_1373_);
v___x_1391_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1374_, v_a_1369_);
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref(v___x_1391_);
if (lean_obj_tag(v_a_1392_) == 1)
{
lean_object* v_val_1393_; lean_object* v_numParams_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_val_1393_ = lean_ctor_get(v_a_1392_, 0);
lean_inc(v_val_1393_);
lean_dec_ref(v_a_1392_);
v_numParams_1394_ = lean_ctor_get(v_val_1393_, 1);
lean_inc(v_numParams_1394_);
lean_dec(v_val_1393_);
v___x_1395_ = l_Lean_Expr_getAppNumArgs(v_e_1365_);
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_add(v_numParams_1394_, v___x_1396_);
lean_dec(v_numParams_1394_);
v___x_1398_ = lean_nat_dec_eq(v___x_1395_, v___x_1397_);
lean_dec(v___x_1397_);
lean_dec(v___x_1395_);
if (v___x_1398_ == 0)
{
lean_dec_ref(v_e_1365_);
v___y_1376_ = v_a_1369_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = l_Lean_Expr_appArg_x21(v_e_1365_);
lean_dec_ref(v_e_1365_);
v___x_1400_ = l_Lean_Meta_isConstructorApp(v___x_1399_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1410_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_unbox(v_a_1401_);
lean_dec(v_a_1401_);
if (v___x_1405_ == 0)
{
lean_del_object(v___x_1403_);
v___y_1376_ = v_a_1369_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_dec(v_declName_1374_);
v___x_1406_ = lean_box(v___x_1372_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_dec(v_declName_1374_);
return v___x_1400_;
}
}
}
else
{
lean_dec(v_a_1392_);
lean_dec_ref(v_e_1365_);
v___y_1376_ = v_a_1369_;
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_st_ref_get(v___y_1376_);
v___x_1378_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_1374_);
if (v___x_1378_ == 0)
{
uint8_t v___x_1379_; 
v___x_1379_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(v_declName_1374_);
if (v___x_1379_ == 0)
{
uint8_t v___x_1380_; 
v___x_1380_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_1374_);
if (v___x_1380_ == 0)
{
lean_object* v_env_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_env_1381_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref(v_env_1381_);
lean_dec(v___x_1377_);
v___x_1382_ = lean_is_matcher(v_env_1381_, v_declName_1374_);
v___x_1383_ = lean_box(v___x_1382_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec(v___x_1377_);
lean_dec(v_declName_1374_);
v___x_1385_ = lean_box(v___x_1372_);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v___x_1377_);
lean_dec(v_declName_1374_);
v___x_1387_ = lean_box(v___x_1372_);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v___x_1377_);
lean_dec(v_declName_1374_);
v___x_1389_ = lean_box(v___x_1372_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
lean_dec_ref(v___x_1373_);
lean_dec_ref(v_e_1365_);
v___x_1411_ = lean_box(v___x_1371_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec_ref(v_e_1365_);
v___x_1413_ = lean_box(v___x_1372_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp___boxed(lean_object* v_e_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Meta_Grind_isSupportApp(v_e_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_object* v___x_1424_; 
v___x_1424_ = l_List_reverse___redArg(v_a_1423_);
return v___x_1424_;
}
else
{
lean_object* v_head_1425_; lean_object* v_tail_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1435_; 
v_head_1425_ = lean_ctor_get(v_a_1422_, 0);
v_tail_1426_ = lean_ctor_get(v_a_1422_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_a_1422_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1428_ = v_a_1422_;
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_tail_1426_);
lean_inc(v_head_1425_);
lean_dec(v_a_1422_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = l_Lean_MessageData_ofExpr(v_head_1425_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 1, v_a_1423_);
lean_ctor_set(v___x_1428_, 0, v___x_1430_);
v___x_1432_ = v___x_1428_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_a_1423_);
v___x_1432_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
v_a_1422_ = v_tail_1426_;
v_a_1423_ = v___x_1432_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__2(void){
_start:
{
lean_object* v___x_1439_; uint8_t v___x_1440_; double v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1439_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1440_ = 1;
v___x_1441_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1442_ = lean_box(0);
v___x_1443_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1444_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v___x_1442_);
lean_ctor_set(v___x_1444_, 2, v___x_1439_);
lean_ctor_set_float(v___x_1444_, sizeof(void*)*3, v___x_1441_);
lean_ctor_set_float(v___x_1444_, sizeof(void*)*3 + 8, v___x_1441_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 16, v___x_1440_);
return v___x_1444_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__5(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__4));
v___x_1449_ = l_Lean_MessageData_ofFormat(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__6(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
v___x_1451_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__5, &l_Lean_Meta_Grind_ppEqc___closed__5_once, _init_l_Lean_Meta_Grind_ppEqc___closed__5);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v___x_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppEqc(lean_object* v_eqc_1453_, lean_object* v_children_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1455_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__2, &l_Lean_Meta_Grind_ppEqc___closed__2_once, _init_l_Lean_Meta_Grind_ppEqc___closed__2);
v___x_1456_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
v___x_1457_ = lean_box(0);
v___x_1458_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(v_eqc_1453_, v___x_1457_);
v___x_1459_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__6, &l_Lean_Meta_Grind_ppEqc___closed__6_once, _init_l_Lean_Meta_Grind_ppEqc___closed__6);
v___x_1460_ = l_Lean_MessageData_joinSep(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1456_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
v___x_1465_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1455_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
lean_ctor_set(v___x_1465_, 2, v_children_1454_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
if (lean_obj_tag(v_a_1466_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = l_List_reverse___redArg(v_a_1467_);
return v___x_1468_;
}
else
{
lean_object* v_head_1469_; lean_object* v_tail_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v_head_1469_ = lean_ctor_get(v_a_1466_, 0);
v_tail_1470_ = lean_ctor_get(v_a_1466_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1466_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1472_ = v_a_1466_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_tail_1470_);
lean_inc(v_head_1469_);
lean_dec(v_a_1466_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
uint8_t v___x_1474_; 
lean_inc(v_head_1469_);
v___x_1474_ = l_Lean_Expr_isTrue(v_head_1469_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1476_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v_a_1467_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_head_1469_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_a_1467_);
v___x_1476_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
v_a_1466_ = v_tail_1470_;
v_a_1467_ = v___x_1476_;
goto _start;
}
}
else
{
lean_del_object(v___x_1472_);
lean_dec(v_head_1469_);
v_a_1466_ = v_tail_1470_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
if (lean_obj_tag(v_a_1481_) == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = l_List_reverse___redArg(v_a_1482_);
return v___x_1483_;
}
else
{
lean_object* v_head_1484_; lean_object* v_tail_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1495_; 
v_head_1484_ = lean_ctor_get(v_a_1481_, 0);
v_tail_1485_ = lean_ctor_get(v_a_1481_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_a_1481_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1487_ = v_a_1481_;
v_isShared_1488_ = v_isSharedCheck_1495_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_tail_1485_);
lean_inc(v_head_1484_);
lean_dec(v_a_1481_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1495_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
uint8_t v___x_1489_; 
lean_inc(v_head_1484_);
v___x_1489_ = l_Lean_Expr_isFalse(v_head_1484_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1491_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v_a_1482_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_head_1484_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_a_1482_);
v___x_1491_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
v_a_1481_ = v_tail_1485_;
v_a_1482_ = v___x_1491_;
goto _start;
}
}
else
{
lean_del_object(v___x_1487_);
lean_dec(v_head_1484_);
v_a_1481_ = v_tail_1485_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___redArg(uint8_t v_a_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
if (lean_obj_tag(v_x_1497_) == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_x_1498_);
lean_ctor_set(v___x_1505_, 1, v___y_1499_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
else
{
lean_object* v_head_1507_; lean_object* v_tail_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1530_; 
v_head_1507_ = lean_ctor_get(v_x_1497_, 0);
v_tail_1508_ = lean_ctor_get(v_x_1497_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_x_1497_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1510_ = v_x_1497_;
v_isShared_1511_ = v_isSharedCheck_1530_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_tail_1508_);
lean_inc(v_head_1507_);
lean_dec(v_x_1497_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1530_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; 
lean_inc(v_head_1507_);
v___x_1512_ = l_Lean_Meta_Grind_isSupportApp(v_head_1507_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v_snd_1515_; uint8_t v___x_1520_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v___x_1512_);
v___x_1520_ = lean_unbox(v_a_1513_);
lean_dec(v_a_1513_);
if (v___x_1520_ == 0)
{
v_snd_1515_ = v___y_1499_;
goto v___jp_1514_;
}
else
{
if (v_a_1496_ == 0)
{
lean_del_object(v___x_1510_);
lean_dec(v_head_1507_);
v_x_1497_ = v_tail_1508_;
goto _start;
}
else
{
v_snd_1515_ = v___y_1499_;
goto v___jp_1514_;
}
}
v___jp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v_x_1498_);
v___x_1517_ = v___x_1510_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_head_1507_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_x_1498_);
v___x_1517_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v_x_1497_ = v_tail_1508_;
v_x_1498_ = v___x_1517_;
v___y_1499_ = v_snd_1515_;
goto _start;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_del_object(v___x_1510_);
lean_dec(v_tail_1508_);
lean_dec(v_head_1507_);
lean_dec_ref(v___y_1499_);
lean_dec(v_x_1498_);
v_a_1522_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1512_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1512_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___redArg___boxed(lean_object* v_a_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
uint8_t v_a_20109__boxed_1540_; lean_object* v_res_1541_; 
v_a_20109__boxed_1540_ = lean_unbox(v_a_1531_);
v_res_1541_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___redArg(v_a_20109__boxed_1540_, v_x_1532_, v_x_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_x_1543_);
lean_ctor_set(v___x_1550_, 1, v___y_1544_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
else
{
lean_object* v_head_1552_; lean_object* v_tail_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1573_; 
v_head_1552_ = lean_ctor_get(v_x_1542_, 0);
v_tail_1553_ = lean_ctor_get(v_x_1542_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1555_ = v_x_1542_;
v_isShared_1556_ = v_isSharedCheck_1573_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_tail_1553_);
lean_inc(v_head_1552_);
lean_dec(v_x_1542_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1573_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; 
lean_inc(v_head_1552_);
v___x_1557_ = l_Lean_Meta_Grind_isSupportApp(v_head_1552_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; uint8_t v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = lean_unbox(v_a_1558_);
lean_dec(v_a_1558_);
if (v___x_1559_ == 0)
{
lean_del_object(v___x_1555_);
lean_dec(v_head_1552_);
v_x_1542_ = v_tail_1553_;
goto _start;
}
else
{
lean_object* v___x_1562_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 1, v_x_1543_);
v___x_1562_ = v___x_1555_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_head_1552_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_x_1543_);
v___x_1562_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
v_x_1542_ = v_tail_1553_;
v_x_1543_ = v___x_1562_;
goto _start;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_del_object(v___x_1555_);
lean_dec(v_tail_1553_);
lean_dec(v_head_1552_);
lean_dec_ref(v___y_1544_);
lean_dec(v_x_1543_);
v_a_1565_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1557_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1557_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg___boxed(lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_x_1574_, v_x_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg(uint8_t v_collapsedProps_1590_, lean_object* v_as_x27_1591_, lean_object* v_b_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
if (lean_obj_tag(v_as_x27_1591_) == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v_b_1592_);
lean_ctor_set(v___x_1600_, 1, v___y_1594_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v_snd_1602_; lean_object* v_snd_1603_; lean_object* v_head_1604_; lean_object* v_tail_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1811_; 
v_snd_1602_ = lean_ctor_get(v_b_1592_, 1);
lean_inc(v_snd_1602_);
v_snd_1603_ = lean_ctor_get(v_snd_1602_, 1);
lean_inc(v_snd_1603_);
v_head_1604_ = lean_ctor_get(v_as_x27_1591_, 0);
v_tail_1605_ = lean_ctor_get(v_as_x27_1591_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_as_x27_1591_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1607_ = v_as_x27_1591_;
v_isShared_1608_ = v_isSharedCheck_1811_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_tail_1605_);
lean_inc(v_head_1604_);
lean_dec(v_as_x27_1591_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1811_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_fst_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1809_; 
v_fst_1609_ = lean_ctor_get(v_b_1592_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_b_1592_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v_b_1592_, 1);
lean_dec(v_unused_1810_);
v___x_1611_ = v_b_1592_;
v_isShared_1612_ = v_isSharedCheck_1809_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_fst_1609_);
lean_dec(v_b_1592_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1809_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_fst_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1807_; 
v_fst_1613_ = lean_ctor_get(v_snd_1602_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_snd_1602_);
if (v_isSharedCheck_1807_ == 0)
{
lean_object* v_unused_1808_; 
v_unused_1808_ = lean_ctor_get(v_snd_1602_, 1);
lean_dec(v_unused_1808_);
v___x_1615_ = v_snd_1602_;
v_isShared_1616_ = v_isSharedCheck_1807_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_fst_1613_);
lean_dec(v_snd_1602_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1807_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1806_; 
v_fst_1617_ = lean_ctor_get(v_snd_1603_, 0);
v_snd_1618_ = lean_ctor_get(v_snd_1603_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_snd_1603_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1620_ = v_snd_1603_;
v_isShared_1621_ = v_isSharedCheck_1806_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_snd_1618_);
lean_inc(v_fst_1617_);
lean_dec(v_snd_1603_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1806_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___y_1623_; lean_object* v___f_1634_; lean_object* v___x_1635_; 
v___f_1634_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__0));
lean_inc(v_head_1604_);
v___x_1635_ = l_List_find_x3f___redArg(v___f_1634_, v_head_1604_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___f_1636_; lean_object* v___x_1637_; 
v___f_1636_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__1));
lean_inc(v_head_1604_);
v___x_1637_ = l_List_find_x3f___redArg(v___f_1636_, v_head_1604_);
if (lean_obj_tag(v___x_1637_) == 0)
{
if (lean_obj_tag(v_head_1604_) == 1)
{
lean_object* v_tail_1638_; 
v_tail_1638_ = lean_ctor_get(v_head_1604_, 1);
lean_inc(v_tail_1638_);
if (lean_obj_tag(v_tail_1638_) == 1)
{
lean_object* v_head_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1747_; 
lean_del_object(v___x_1620_);
lean_del_object(v___x_1615_);
lean_del_object(v___x_1611_);
v_head_1639_ = lean_ctor_get(v_head_1604_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_tail_1638_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; lean_object* v_unused_1749_; 
v_unused_1748_ = lean_ctor_get(v_tail_1638_, 1);
lean_dec(v_unused_1748_);
v_unused_1749_ = lean_ctor_get(v_tail_1638_, 0);
lean_dec(v_unused_1749_);
v___x_1641_ = v_tail_1638_;
v_isShared_1642_ = v_isSharedCheck_1747_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v_tail_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1747_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; 
lean_inc(v_head_1639_);
v___x_1643_ = l_Lean_Meta_isProof(v_head_1639_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; uint8_t v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = lean_unbox(v_a_1644_);
if (v___x_1645_ == 0)
{
lean_object* v_regularEqcs_1646_; lean_object* v___y_1648_; lean_object* v_fst_1649_; lean_object* v_snd_1650_; lean_object* v_fst_1677_; lean_object* v_snd_1678_; lean_object* v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; 
v_regularEqcs_1646_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1705_ = lean_box(0);
v___x_1706_ = lean_unbox(v_a_1644_);
lean_dec(v_a_1644_);
lean_inc_ref(v_head_1604_);
v___x_1707_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___redArg(v___x_1706_, v_head_1604_, v___x_1705_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v_fst_1709_; lean_object* v_snd_1710_; lean_object* v___x_1711_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v___x_1707_);
v_fst_1709_ = lean_ctor_get(v_a_1708_, 0);
lean_inc(v_fst_1709_);
v_snd_1710_ = lean_ctor_get(v_a_1708_, 1);
lean_inc(v_snd_1710_);
lean_dec(v_a_1708_);
v___x_1711_ = l_List_reverse___redArg(v_fst_1709_);
v_fst_1677_ = v___x_1711_;
v_snd_1678_ = v_snd_1710_;
goto v___jp_1676_;
}
else
{
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1712_; lean_object* v_fst_1713_; lean_object* v_snd_1714_; 
v_a_1712_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1712_);
lean_dec_ref(v___x_1707_);
v_fst_1713_ = lean_ctor_get(v_a_1712_, 0);
lean_inc(v_fst_1713_);
v_snd_1714_ = lean_ctor_get(v_a_1712_, 1);
lean_inc(v_snd_1714_);
lean_dec(v_a_1712_);
v_fst_1677_ = v_fst_1713_;
v_snd_1678_ = v_snd_1714_;
goto v___jp_1676_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_del_object(v___x_1641_);
lean_dec_ref(v_head_1604_);
lean_dec(v_snd_1618_);
lean_dec(v_fst_1617_);
lean_dec(v_fst_1613_);
lean_dec(v_fst_1609_);
lean_del_object(v___x_1607_);
lean_dec(v_tail_1605_);
v_a_1715_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1707_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1707_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
v___jp_1647_:
{
uint8_t v___x_1651_; 
v___x_1651_ = l_List_isEmpty___redArg(v_fst_1649_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1652_ = l_Lean_Meta_Grind_ppEqc(v_fst_1649_, v_regularEqcs_1646_);
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_mk_empty_array_with_capacity(v___x_1653_);
v___x_1655_ = lean_array_push(v___x_1654_, v___x_1652_);
v___x_1656_ = l_Lean_Meta_Grind_ppEqc(v___y_1648_, v___x_1655_);
v___x_1657_ = lean_array_push(v_fst_1617_, v___x_1656_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 0);
lean_ctor_set(v___x_1641_, 1, v_snd_1618_);
lean_ctor_set(v___x_1641_, 0, v___x_1657_);
v___x_1659_ = v___x_1641_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_snd_1618_);
v___x_1659_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 1, v___x_1659_);
lean_ctor_set(v___x_1607_, 0, v_fst_1613_);
v___x_1661_ = v___x_1607_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_fst_1613_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v_fst_1609_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1662_;
v___y_1594_ = v_snd_1650_;
goto _start;
}
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_dec(v_fst_1649_);
v___x_1666_ = l_Lean_Meta_Grind_ppEqc(v___y_1648_, v_regularEqcs_1646_);
v___x_1667_ = lean_array_push(v_fst_1617_, v___x_1666_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 0);
lean_ctor_set(v___x_1641_, 1, v_snd_1618_);
lean_ctor_set(v___x_1641_, 0, v___x_1667_);
v___x_1669_ = v___x_1641_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_snd_1618_);
v___x_1669_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 1, v___x_1669_);
lean_ctor_set(v___x_1607_, 0, v_fst_1613_);
v___x_1671_ = v___x_1607_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_fst_1613_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_fst_1609_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1672_;
v___y_1594_ = v_snd_1650_;
goto _start;
}
}
}
}
v___jp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1679_ = l_List_lengthTR___redArg(v_fst_1677_);
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_dec_le(v___x_1679_, v___x_1680_);
lean_dec(v___x_1679_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_box(0);
v___x_1683_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_head_1604_, v___x_1682_, v_snd_1678_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v_fst_1685_; lean_object* v_snd_1686_; lean_object* v___x_1687_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v_fst_1685_ = lean_ctor_get(v_a_1684_, 0);
lean_inc(v_fst_1685_);
v_snd_1686_ = lean_ctor_get(v_a_1684_, 1);
lean_inc(v_snd_1686_);
lean_dec(v_a_1684_);
v___x_1687_ = l_List_reverse___redArg(v_fst_1685_);
v___y_1648_ = v_fst_1677_;
v_fst_1649_ = v___x_1687_;
v_snd_1650_ = v_snd_1686_;
goto v___jp_1647_;
}
else
{
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1688_; lean_object* v_fst_1689_; lean_object* v_snd_1690_; 
v_a_1688_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1683_);
v_fst_1689_ = lean_ctor_get(v_a_1688_, 0);
lean_inc(v_fst_1689_);
v_snd_1690_ = lean_ctor_get(v_a_1688_, 1);
lean_inc(v_snd_1690_);
lean_dec(v_a_1688_);
v___y_1648_ = v_fst_1677_;
v_fst_1649_ = v_fst_1689_;
v_snd_1650_ = v_snd_1690_;
goto v___jp_1647_;
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_fst_1677_);
lean_del_object(v___x_1641_);
lean_dec(v_snd_1618_);
lean_dec(v_fst_1617_);
lean_dec(v_fst_1613_);
lean_dec(v_fst_1609_);
lean_del_object(v___x_1607_);
lean_dec(v_tail_1605_);
v_a_1691_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1683_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1683_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
lean_dec(v_fst_1677_);
lean_del_object(v___x_1641_);
lean_del_object(v___x_1607_);
v___x_1699_ = l_Lean_Meta_Grind_ppEqc(v_head_1604_, v_regularEqcs_1646_);
v___x_1700_ = lean_array_push(v_snd_1618_, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_fst_1617_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v_fst_1613_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_fst_1609_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1703_;
v___y_1594_ = v_snd_1678_;
goto _start;
}
}
}
else
{
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_a_1644_);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_head_1604_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; lean_object* v_unused_1738_; 
v_unused_1737_ = lean_ctor_get(v_head_1604_, 1);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_head_1604_, 0);
lean_dec(v_unused_1738_);
v___x_1724_ = v_head_1604_;
v_isShared_1725_ = v_isSharedCheck_1736_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v_head_1604_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1736_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 0);
lean_ctor_set(v___x_1641_, 1, v_snd_1618_);
lean_ctor_set(v___x_1641_, 0, v_fst_1617_);
v___x_1727_ = v___x_1641_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_snd_1618_);
v___x_1727_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 0);
lean_ctor_set(v___x_1724_, 1, v___x_1727_);
lean_ctor_set(v___x_1724_, 0, v_fst_1613_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_fst_1613_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1731_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 1, v___x_1729_);
lean_ctor_set(v___x_1607_, 0, v_fst_1609_);
v___x_1731_ = v___x_1607_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_fst_1609_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1731_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_del_object(v___x_1641_);
lean_dec_ref(v_head_1604_);
lean_dec(v_snd_1618_);
lean_dec(v_fst_1617_);
lean_dec(v_fst_1613_);
lean_dec(v_fst_1609_);
lean_del_object(v___x_1607_);
lean_dec(v_tail_1605_);
lean_dec_ref(v___y_1594_);
v_a_1739_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1643_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1643_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
else
{
lean_dec_ref(v_head_1604_);
lean_dec(v_tail_1638_);
lean_del_object(v___x_1607_);
v___y_1623_ = v___y_1594_;
goto v___jp_1622_;
}
}
else
{
lean_del_object(v___x_1607_);
lean_dec(v_head_1604_);
v___y_1623_ = v___y_1594_;
goto v___jp_1622_;
}
}
else
{
lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1776_; 
lean_del_object(v___x_1620_);
lean_del_object(v___x_1615_);
lean_del_object(v___x_1611_);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v___x_1637_, 0);
lean_dec(v_unused_1777_);
v___x_1751_ = v___x_1637_;
v_isShared_1752_ = v_isSharedCheck_1776_;
goto v_resetjp_1750_;
}
else
{
lean_dec(v___x_1637_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1776_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = lean_box(0);
v___x_1754_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(v_head_1604_, v___x_1753_);
v___x_1755_ = l_List_isEmpty___redArg(v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
lean_dec(v_fst_1613_);
v___x_1756_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1757_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__2));
v___x_1758_ = lean_array_mk(v___x_1754_);
v___x_1759_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__4));
v___x_1760_ = l_Lean_Meta_Grind_ppExprArray(v___x_1756_, v___x_1757_, v___x_1758_, v___x_1759_, v_collapsedProps_1590_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1760_);
v___x_1762_ = v___x_1751_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1764_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 1, v_snd_1618_);
lean_ctor_set(v___x_1607_, 0, v_fst_1617_);
v___x_1764_ = v___x_1607_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_snd_1618_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1762_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_fst_1609_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1766_;
goto _start;
}
}
}
else
{
lean_object* v___x_1771_; 
lean_dec(v___x_1754_);
lean_del_object(v___x_1751_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 1, v_snd_1618_);
lean_ctor_set(v___x_1607_, 0, v_fst_1617_);
v___x_1771_ = v___x_1607_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_snd_1618_);
v___x_1771_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_fst_1613_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v_fst_1609_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1773_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1804_; 
lean_del_object(v___x_1620_);
lean_del_object(v___x_1615_);
lean_del_object(v___x_1611_);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v___x_1635_, 0);
lean_dec(v_unused_1805_);
v___x_1779_ = v___x_1635_;
v_isShared_1780_ = v_isSharedCheck_1804_;
goto v_resetjp_1778_;
}
else
{
lean_dec(v___x_1635_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1804_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1781_ = lean_box(0);
v___x_1782_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(v_head_1604_, v___x_1781_);
v___x_1783_ = l_List_isEmpty___redArg(v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_dec(v_fst_1609_);
v___x_1784_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1785_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__5));
v___x_1786_ = lean_array_mk(v___x_1782_);
v___x_1787_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__4));
v___x_1788_ = l_Lean_Meta_Grind_ppExprArray(v___x_1784_, v___x_1785_, v___x_1786_, v___x_1787_, v_collapsedProps_1590_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1788_);
v___x_1790_ = v___x_1779_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 1, v_snd_1618_);
lean_ctor_set(v___x_1607_, 0, v_fst_1617_);
v___x_1792_ = v___x_1607_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_snd_1618_);
v___x_1792_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_fst_1613_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1790_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1794_;
goto _start;
}
}
}
else
{
lean_object* v___x_1799_; 
lean_dec(v___x_1782_);
lean_del_object(v___x_1779_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 1, v_snd_1618_);
lean_ctor_set(v___x_1607_, 0, v_fst_1617_);
v___x_1799_ = v___x_1607_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_snd_1618_);
v___x_1799_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v_fst_1613_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v_fst_1609_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1801_;
goto _start;
}
}
}
}
v___jp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1621_ == 0)
{
v___x_1625_ = v___x_1620_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_snd_1618_);
v___x_1625_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1627_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 1, v___x_1625_);
v___x_1627_ = v___x_1615_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_fst_1613_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1629_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v___x_1627_);
v___x_1629_ = v___x_1611_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_fst_1609_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
v_as_x27_1591_ = v_tail_1605_;
v_b_1592_ = v___x_1629_;
v___y_1594_ = v___y_1623_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___boxed(lean_object* v_collapsedProps_1812_, lean_object* v_as_x27_1813_, lean_object* v_b_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v_collapsedProps_boxed_1822_; lean_object* v_res_1823_; 
v_collapsedProps_boxed_1822_ = lean_unbox(v_collapsedProps_1812_);
v_res_1823_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg(v_collapsedProps_boxed_1822_, v_as_x27_1813_, v_b_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___y_1815_);
return v_res_1823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0(void){
_start:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; double v___x_1826_; lean_object* v_trueEqc_x3f_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1824_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1825_ = 1;
v___x_1826_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v_trueEqc_x3f_1827_ = lean_box(0);
v___x_1828_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1829_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v_trueEqc_x3f_1827_);
lean_ctor_set(v___x_1829_, 2, v___x_1824_);
lean_ctor_set_float(v___x_1829_, sizeof(void*)*3, v___x_1826_);
lean_ctor_set_float(v___x_1829_, sizeof(void*)*3 + 8, v___x_1826_);
lean_ctor_set_uint8(v___x_1829_, sizeof(void*)*3 + 16, v___x_1825_);
return v___x_1829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2));
v___x_1834_ = l_Lean_MessageData_ofFormat(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8));
v___x_1847_ = l_Lean_MessageData_ofFormat(v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(uint8_t v_collapsedProps_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___x_1856_; uint8_t v___x_1857_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = 1;
lean_inc_ref(v_a_1849_);
v___x_1870_ = l_Lean_Meta_Grind_Goal_getEqcs(v_a_1849_, v___x_1857_);
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6));
v___x_1872_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg(v_collapsedProps_1848_, v___x_1870_, v___x_1871_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v_snd_1876_; lean_object* v_fst_1877_; lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v_regularEqcs_1888_; lean_object* v___y_1889_; lean_object* v_fst_1894_; lean_object* v_snd_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v_fst_1874_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_fst_1874_);
v_snd_1875_ = lean_ctor_get(v_fst_1874_, 1);
lean_inc(v_snd_1875_);
v_snd_1876_ = lean_ctor_get(v_a_1873_, 1);
lean_inc(v_snd_1876_);
lean_dec(v_a_1873_);
v_fst_1877_ = lean_ctor_get(v_fst_1874_, 0);
lean_inc(v_fst_1877_);
lean_dec(v_fst_1874_);
v_fst_1878_ = lean_ctor_get(v_snd_1875_, 0);
lean_inc(v_fst_1878_);
v_snd_1879_ = lean_ctor_get(v_snd_1875_, 1);
lean_inc(v_snd_1879_);
lean_dec(v_snd_1875_);
v_fst_1894_ = lean_ctor_get(v_snd_1879_, 0);
lean_inc(v_fst_1894_);
v_snd_1895_ = lean_ctor_get(v_snd_1879_, 1);
lean_inc(v_snd_1895_);
lean_dec(v_snd_1879_);
v___x_1896_ = lean_array_get_size(v_snd_1895_);
v___x_1897_ = lean_nat_dec_eq(v___x_1896_, v___x_1856_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
v___x_1899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9);
v___x_1900_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
lean_ctor_set(v___x_1900_, 2, v_snd_1895_);
v___x_1901_ = lean_array_push(v_fst_1894_, v___x_1900_);
v_regularEqcs_1888_ = v___x_1901_;
v___y_1889_ = v_snd_1876_;
goto v___jp_1887_;
}
else
{
lean_dec(v_snd_1895_);
v_regularEqcs_1888_ = v_fst_1894_;
v___y_1889_ = v_snd_1876_;
goto v___jp_1887_;
}
v___jp_1880_:
{
if (lean_obj_tag(v_fst_1878_) == 1)
{
lean_object* v_val_1883_; lean_object* v___x_1884_; lean_object* v_a_1885_; lean_object* v_snd_1886_; 
v_val_1883_ = lean_ctor_get(v_fst_1878_, 0);
lean_inc(v_val_1883_);
lean_dec_ref(v_fst_1878_);
v___x_1884_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_1883_, v___y_1882_);
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v_snd_1886_ = lean_ctor_get(v_a_1885_, 1);
lean_inc(v_snd_1886_);
lean_dec(v_a_1885_);
v___y_1859_ = v___y_1881_;
v___y_1860_ = v_snd_1886_;
goto v___jp_1858_;
}
else
{
lean_dec(v_fst_1878_);
v___y_1859_ = v___y_1881_;
v___y_1860_ = v___y_1882_;
goto v___jp_1858_;
}
}
v___jp_1887_:
{
if (lean_obj_tag(v_fst_1877_) == 1)
{
lean_object* v_val_1890_; lean_object* v___x_1891_; lean_object* v_a_1892_; lean_object* v_snd_1893_; 
v_val_1890_ = lean_ctor_get(v_fst_1877_, 0);
lean_inc(v_val_1890_);
lean_dec_ref(v_fst_1877_);
v___x_1891_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_1890_, v___y_1889_);
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
v_snd_1893_ = lean_ctor_get(v_a_1892_, 1);
lean_inc(v_snd_1893_);
lean_dec(v_a_1892_);
v___y_1881_ = v_regularEqcs_1888_;
v___y_1882_ = v_snd_1893_;
goto v___jp_1880_;
}
else
{
lean_dec(v_fst_1877_);
v___y_1881_ = v_regularEqcs_1888_;
v___y_1882_ = v___y_1889_;
goto v___jp_1880_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1872_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1872_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
v___jp_1858_:
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_array_get_size(v___y_1859_);
v___x_1862_ = lean_nat_dec_eq(v___x_1861_, v___x_1856_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
v___x_1864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3);
v___x_1865_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
lean_ctor_set(v___x_1865_, 2, v___y_1859_);
v___x_1866_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_1865_, v___y_1860_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v___y_1859_);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___y_1860_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___boxed(lean_object* v_collapsedProps_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
uint8_t v_collapsedProps_boxed_1918_; lean_object* v_res_1919_; 
v_collapsedProps_boxed_1918_ = lean_unbox(v_collapsedProps_1910_);
v_res_1919_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(v_collapsedProps_boxed_1918_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec_ref(v_a_1911_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_x_1920_, v_x_1921_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___boxed(lean_object* v_x_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(v_x_1930_, v_x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec_ref(v___y_1932_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(uint8_t v_a_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___redArg(v_a_1940_, v_x_1941_, v_x_1942_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___boxed(lean_object* v_a_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
uint8_t v_a_20940__boxed_1961_; lean_object* v_res_1962_; 
v_a_20940__boxed_1961_ = lean_unbox(v_a_1951_);
v_res_1962_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(v_a_20940__boxed_1961_, v_x_1952_, v_x_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec_ref(v___y_1954_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(uint8_t v_collapsedProps_1963_, lean_object* v_as_1964_, lean_object* v_as_x27_1965_, lean_object* v_b_1966_, lean_object* v_a_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg(v_collapsedProps_1963_, v_as_x27_1965_, v_b_1966_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___boxed(lean_object* v_collapsedProps_1976_, lean_object* v_as_1977_, lean_object* v_as_x27_1978_, lean_object* v_b_1979_, lean_object* v_a_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
uint8_t v_collapsedProps_boxed_1988_; lean_object* v_res_1989_; 
v_collapsedProps_boxed_1988_ = lean_unbox(v_collapsedProps_1976_);
v_res_1989_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(v_collapsedProps_boxed_1988_, v_as_1977_, v_as_x27_1978_, v_b_1979_, v_a_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec_ref(v___y_1981_);
lean_dec(v_as_1977_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
if (lean_obj_tag(v_a_1990_) == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = l_List_reverse___redArg(v_a_1991_);
return v___x_1992_;
}
else
{
lean_object* v_head_1993_; lean_object* v_tail_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2003_; 
v_head_1993_ = lean_ctor_get(v_a_1990_, 0);
v_tail_1994_ = lean_ctor_get(v_a_1990_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_a_1990_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1996_ = v_a_1990_;
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_tail_1994_);
lean_inc(v_head_1993_);
lean_dec(v_a_1990_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = l_Lean_Meta_Grind_ppPattern(v_head_1993_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v_a_1991_);
lean_ctor_set(v___x_1996_, 0, v___x_1998_);
v___x_2000_ = v___x_1996_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_a_1991_);
v___x_2000_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
v_a_1990_ = v_tail_1994_;
v_a_1991_ = v___x_2000_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
if (lean_obj_tag(v_a_2004_) == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = l_List_reverse___redArg(v_a_2005_);
return v___x_2006_;
}
else
{
lean_object* v_head_2007_; lean_object* v_tail_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v_head_2007_ = lean_ctor_get(v_a_2004_, 0);
v_tail_2008_ = lean_ctor_get(v_a_2004_, 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v_a_2004_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_tail_2008_);
lean_inc(v_head_2007_);
lean_dec(v_a_2004_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_a_2005_);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_head_2007_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_a_2005_);
v___x_2013_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
v_a_2004_ = v_tail_2008_;
v_a_2005_ = v___x_2013_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0));
v___x_2019_ = l_Lean_stringToMessageData(v___x_2018_);
return v___x_2019_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4(void){
_start:
{
lean_object* v___x_2023_; uint8_t v___x_2024_; double v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2023_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2024_ = 1;
v___x_2025_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2026_ = lean_box(0);
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3));
v___x_2028_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2026_);
lean_ctor_set(v___x_2028_, 2, v___x_2023_);
lean_ctor_set_float(v___x_2028_, sizeof(void*)*3, v___x_2025_);
lean_ctor_set_float(v___x_2028_, sizeof(void*)*3 + 8, v___x_2025_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*3 + 16, v___x_2024_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(lean_object* v_thm_2029_){
_start:
{
lean_object* v_patterns_2031_; lean_object* v_origin_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v_m_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v_patterns_2031_ = lean_ctor_get(v_thm_2029_, 3);
lean_inc(v_patterns_2031_);
v_origin_2032_ = lean_ctor_get(v_thm_2029_, 5);
lean_inc_ref(v_origin_2032_);
lean_dec_ref(v_thm_2029_);
v___x_2033_ = l_Lean_Meta_Grind_Origin_pp(v_origin_2032_);
v___x_2034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = lean_box(0);
v___x_2037_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(v_patterns_2031_, v___x_2036_);
v___x_2038_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(v___x_2037_, v___x_2036_);
v___x_2039_ = l_Lean_MessageData_ofList(v___x_2038_);
v_m_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_2040_, 0, v___x_2035_);
lean_ctor_set(v_m_2040_, 1, v___x_2039_);
v___x_2041_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4);
v___x_2042_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2043_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v_m_2040_);
lean_ctor_set(v___x_2043_, 2, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___boxed(lean_object* v_thm_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_thm_2045_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(lean_object* v_thm_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_thm_2048_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___boxed(lean_object* v_thm_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(v_thm_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(size_t v_sz_2062_, size_t v_i_2063_, lean_object* v_bs_2064_, lean_object* v___y_2065_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_usize_dec_lt(v_i_2063_, v_sz_2062_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_bs_2064_);
lean_ctor_set(v___x_2068_, 1, v___y_2065_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
else
{
lean_object* v_v_2070_; lean_object* v___x_2071_; 
v_v_2070_ = lean_array_uget_borrowed(v_bs_2064_, v_i_2063_);
lean_inc(v_v_2070_);
v___x_2071_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_v_2070_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; lean_object* v_bs_x27_2074_; size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
v___x_2073_ = lean_unsigned_to_nat(0u);
v_bs_x27_2074_ = lean_array_uset(v_bs_2064_, v_i_2063_, v___x_2073_);
v___x_2075_ = ((size_t)1ULL);
v___x_2076_ = lean_usize_add(v_i_2063_, v___x_2075_);
v___x_2077_ = lean_array_uset(v_bs_x27_2074_, v_i_2063_, v_a_2072_);
v_i_2063_ = v___x_2076_;
v_bs_2064_ = v___x_2077_;
goto _start;
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_bs_2064_);
v_a_2079_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2071_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2071_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg___boxed(lean_object* v_sz_2087_, lean_object* v_i_2088_, lean_object* v_bs_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
size_t v_sz_boxed_2092_; size_t v_i_boxed_2093_; lean_object* v_res_2094_; 
v_sz_boxed_2092_ = lean_unbox_usize(v_sz_2087_);
lean_dec(v_sz_2087_);
v_i_boxed_2093_ = lean_unbox_usize(v_i_2088_);
lean_dec(v_i_2088_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_boxed_2092_, v_i_boxed_2093_, v_bs_2089_, v___y_2090_);
return v_res_2094_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2(void){
_start:
{
lean_object* v___x_2098_; uint8_t v___x_2099_; double v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2098_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2099_ = 1;
v___x_2100_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2101_ = lean_box(0);
v___x_2102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1));
v___x_2103_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
lean_ctor_set(v___x_2103_, 2, v___x_2098_);
lean_ctor_set_float(v___x_2103_, sizeof(void*)*3, v___x_2100_);
lean_ctor_set_float(v___x_2103_, sizeof(void*)*3 + 8, v___x_2100_);
lean_ctor_set_uint8(v___x_2103_, sizeof(void*)*3 + 16, v___x_2099_);
return v___x_2103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4));
v___x_2108_ = l_Lean_MessageData_ofFormat(v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_toGoalState_2116_; lean_object* v_ematch_2117_; lean_object* v_thms_2118_; lean_object* v_newThms_2119_; lean_object* v___x_2120_; size_t v_sz_2121_; size_t v___x_2122_; lean_object* v___x_2123_; 
v_toGoalState_2116_ = lean_ctor_get(v_a_2109_, 0);
v_ematch_2117_ = lean_ctor_get(v_toGoalState_2116_, 12);
v_thms_2118_ = lean_ctor_get(v_ematch_2117_, 2);
v_newThms_2119_ = lean_ctor_get(v_ematch_2117_, 3);
v___x_2120_ = l_Lean_PersistentArray_toArray___redArg(v_thms_2118_);
v_sz_2121_ = lean_array_size(v___x_2120_);
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2121_, v___x_2122_, v___x_2120_, v_a_2110_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v_fst_2125_; lean_object* v_snd_2126_; lean_object* v___x_2127_; size_t v_sz_2128_; lean_object* v___x_2129_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2123_);
v_fst_2125_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_fst_2125_);
v_snd_2126_ = lean_ctor_get(v_a_2124_, 1);
lean_inc(v_snd_2126_);
lean_dec(v_a_2124_);
v___x_2127_ = l_Lean_PersistentArray_toArray___redArg(v_newThms_2119_);
v_sz_2128_ = lean_array_size(v___x_2127_);
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2128_, v___x_2122_, v___x_2127_, v_snd_2126_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2155_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2155_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2155_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_fst_2134_; lean_object* v_snd_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2154_; 
v_fst_2134_ = lean_ctor_get(v_a_2130_, 0);
v_snd_2135_ = lean_ctor_get(v_a_2130_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_a_2130_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2137_ = v_a_2130_;
v_isShared_2138_ = v_isSharedCheck_2154_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_snd_2135_);
lean_inc(v_fst_2134_);
lean_dec(v_a_2130_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2154_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2139_ = l_Array_append___redArg(v_fst_2125_, v_fst_2134_);
lean_dec(v_fst_2134_);
v___x_2140_ = lean_array_get_size(v___x_2139_);
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_nat_dec_eq(v___x_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_del_object(v___x_2137_);
lean_del_object(v___x_2132_);
v___x_2143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2);
v___x_2144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5);
v___x_2145_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
lean_ctor_set(v___x_2145_, 2, v___x_2139_);
v___x_2146_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2145_, v_snd_2135_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
lean_dec_ref(v___x_2139_);
v___x_2147_ = lean_box(0);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2147_);
v___x_2149_ = v___x_2137_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_snd_2135_);
v___x_2149_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2149_);
v___x_2151_ = v___x_2132_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_fst_2125_);
v_a_2156_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2129_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2129_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_a_2164_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2123_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2123_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___boxed(lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec_ref(v_a_2172_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(size_t v_sz_2180_, size_t v_i_2181_, lean_object* v_bs_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2180_, v_i_2181_, v_bs_2182_, v___y_2184_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___boxed(lean_object* v_sz_2191_, lean_object* v_i_2192_, lean_object* v_bs_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
size_t v_sz_boxed_2201_; size_t v_i_boxed_2202_; lean_object* v_res_2203_; 
v_sz_boxed_2201_ = lean_unbox_usize(v_sz_2191_);
lean_dec(v_sz_2191_);
v_i_boxed_2202_ = lean_unbox_usize(v_i_2192_);
lean_dec(v_i_2192_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(v_sz_boxed_2201_, v_i_boxed_2202_, v_bs_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec_ref(v___y_2194_);
return v_res_2203_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(lean_object* v_x_2204_){
_start:
{
uint8_t v___x_2205_; 
v___x_2205_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg___boxed(lean_object* v_x_2206_){
_start:
{
uint8_t v_res_2207_; lean_object* v_r_2208_; 
v_res_2207_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(v_x_2206_);
lean_dec_ref(v_x_2206_);
v_r_2208_ = lean_box(v_res_2207_);
return v_r_2208_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(lean_object* v_00_u03b2_2209_, lean_object* v_x_2210_){
_start:
{
uint8_t v___x_2211_; 
v___x_2211_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___boxed(lean_object* v_00_u03b2_2212_, lean_object* v_x_2213_){
_start:
{
uint8_t v_res_2214_; lean_object* v_r_2215_; 
v_res_2214_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(v_00_u03b2_2212_, v_x_2213_);
lean_dec_ref(v_x_2213_);
v_r_2215_ = lean_box(v_res_2214_);
return v_r_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(lean_object* v_as_2220_, size_t v_sz_2221_, size_t v_i_2222_, lean_object* v_b_2223_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_usize_dec_lt(v_i_2222_, v_sz_2221_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_b_2223_);
return v___x_2226_;
}
else
{
lean_object* v_a_2227_; lean_object* v_fst_2228_; lean_object* v_snd_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2270_; 
v_a_2227_ = lean_array_uget(v_as_2220_, v_i_2222_);
v_fst_2228_ = lean_ctor_get(v_a_2227_, 0);
v_snd_2229_ = lean_ctor_get(v_a_2227_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_a_2227_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2231_ = v_a_2227_;
v_isShared_2232_ = v_isSharedCheck_2270_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_snd_2229_);
lean_inc(v_fst_2228_);
lean_dec(v_a_2227_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2270_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; double v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v_num_2239_; lean_object* v_den_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2269_; 
v___x_2233_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1));
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2237_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2238_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2238_, 0, v___x_2234_);
lean_ctor_set(v___x_2238_, 1, v___x_2235_);
lean_ctor_set(v___x_2238_, 2, v___x_2237_);
lean_ctor_set_float(v___x_2238_, sizeof(void*)*3, v___x_2236_);
lean_ctor_set_float(v___x_2238_, sizeof(void*)*3 + 8, v___x_2236_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*3 + 16, v___x_2225_);
v_num_2239_ = lean_ctor_get(v_snd_2229_, 0);
v_den_2240_ = lean_ctor_get(v_snd_2229_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_snd_2229_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2242_ = v_snd_2229_;
v_isShared_2243_ = v_isSharedCheck_2269_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_den_2240_);
lean_inc(v_num_2239_);
lean_dec(v_snd_2229_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2269_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2244_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2228_);
v___x_2245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 7);
lean_ctor_set(v___x_2242_, 1, v___x_2245_);
lean_ctor_set(v___x_2242_, 0, v___x_2244_);
v___x_2247_ = v___x_2242_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___y_2249_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = lean_nat_dec_eq(v_den_2240_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2262_ = l_Int_repr(v_num_2239_);
lean_dec(v_num_2239_);
v___x_2263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2));
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
v___x_2265_ = l_Nat_reprFast(v_den_2240_);
v___x_2266_ = lean_string_append(v___x_2264_, v___x_2265_);
lean_dec_ref(v___x_2265_);
v___y_2249_ = v___x_2266_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2267_; 
lean_dec(v_den_2240_);
v___x_2267_ = l_Int_repr(v_num_2239_);
lean_dec(v_num_2239_);
v___y_2249_ = v___x_2267_;
goto v___jp_2248_;
}
v___jp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___y_2249_);
v___x_2251_ = l_Lean_MessageData_ofFormat(v___x_2250_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 7);
lean_ctor_set(v___x_2231_, 1, v___x_2251_);
lean_ctor_set(v___x_2231_, 0, v___x_2247_);
v___x_2253_ = v___x_2231_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; size_t v___x_2256_; size_t v___x_2257_; 
v___x_2254_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2238_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
lean_ctor_set(v___x_2254_, 2, v___x_2233_);
v___x_2255_ = lean_array_push(v_b_2223_, v___x_2254_);
v___x_2256_ = ((size_t)1ULL);
v___x_2257_ = lean_usize_add(v_i_2222_, v___x_2256_);
v_i_2222_ = v___x_2257_;
v_b_2223_ = v___x_2255_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___boxed(lean_object* v_as_2271_, lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_b_2274_, lean_object* v___y_2275_){
_start:
{
size_t v_sz_boxed_2276_; size_t v_i_boxed_2277_; lean_object* v_res_2278_; 
v_sz_boxed_2276_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2277_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_2271_, v_sz_boxed_2276_, v_i_boxed_2277_, v_b_2274_);
lean_dec_ref(v_as_2271_);
return v_res_2278_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2(void){
_start:
{
lean_object* v___x_2282_; uint8_t v___x_2283_; double v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2282_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2283_ = 1;
v___x_2284_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2285_ = lean_box(0);
v___x_2286_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1));
v___x_2287_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v___x_2285_);
lean_ctor_set(v___x_2287_, 2, v___x_2282_);
lean_ctor_set_float(v___x_2287_, sizeof(void*)*3, v___x_2284_);
lean_ctor_set_float(v___x_2287_, sizeof(void*)*3 + 8, v___x_2284_);
lean_ctor_set_uint8(v___x_2287_, sizeof(void*)*3 + 16, v___x_2283_);
return v___x_2287_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4));
v___x_2292_ = l_Lean_MessageData_ofFormat(v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(lean_object* v_goal_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2300_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2299_, v_goal_2293_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2356_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2356_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2356_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_varMap_2305_; uint8_t v___x_2306_; 
v_varMap_2305_ = lean_ctor_get(v_a_2301_, 1);
lean_inc_ref(v_varMap_2305_);
lean_dec(v_a_2301_);
v___x_2306_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_varMap_2305_);
lean_dec_ref(v_varMap_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; 
lean_del_object(v___x_2303_);
v___x_2307_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2343_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2343_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2343_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2312_ = lean_array_get_size(v_a_2308_);
v___x_2313_ = lean_unsigned_to_nat(0u);
v___x_2314_ = lean_nat_dec_eq(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; size_t v_sz_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
lean_del_object(v___x_2310_);
v___x_2315_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v_sz_2316_ = lean_array_size(v_a_2308_);
v___x_2317_ = ((size_t)0ULL);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_a_2308_, v_sz_2316_, v___x_2317_, v___x_2315_);
lean_dec(v_a_2308_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2330_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2330_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2323_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2);
v___x_2324_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5);
v___x_2325_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
lean_ctor_set(v___x_2325_, 2, v_a_2319_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2326_);
v___x_2328_ = v___x_2321_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v_a_2331_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2318_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2318_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
lean_dec(v_a_2308_);
v___x_2339_ = lean_box(0);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2339_);
v___x_2341_ = v___x_2310_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2307_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2307_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_dec_ref(v_goal_2293_);
v___x_2352_ = lean_box(0);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2352_);
v___x_2354_ = v___x_2303_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_goal_2293_);
v_a_2357_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2359_ = v___x_2300_;
v_isShared_2360_ = v_isSharedCheck_2369_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2300_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2369_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v_ref_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v_ref_2361_ = lean_ctor_get(v_a_2296_, 5);
v___x_2362_ = lean_io_error_to_string(v_a_2357_);
v___x_2363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
v___x_2364_ = l_Lean_MessageData_ofFormat(v___x_2363_);
lean_inc(v_ref_2361_);
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v_ref_2361_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2365_);
v___x_2367_ = v___x_2359_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___boxed(lean_object* v_goal_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(v_goal_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(lean_object* v_as_2377_, size_t v_sz_2378_, size_t v_i_2379_, lean_object* v_b_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_2377_, v_sz_2378_, v_i_2379_, v_b_2380_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___boxed(lean_object* v_as_2387_, lean_object* v_sz_2388_, lean_object* v_i_2389_, lean_object* v_b_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
size_t v_sz_boxed_2396_; size_t v_i_boxed_2397_; lean_object* v_res_2398_; 
v_sz_boxed_2396_ = lean_unbox_usize(v_sz_2388_);
lean_dec(v_sz_2388_);
v_i_boxed_2397_ = lean_unbox_usize(v_i_2389_);
lean_dec(v_i_2389_);
v_res_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(v_as_2387_, v_sz_boxed_2396_, v_i_boxed_2397_, v_b_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec_ref(v_as_2387_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2406_; 
lean_inc_ref(v_a_2399_);
v___x_2406_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(v_a_2399_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2418_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
if (lean_obj_tag(v_a_2407_) == 1)
{
lean_object* v_val_2411_; lean_object* v___x_2412_; 
lean_del_object(v___x_2409_);
v_val_2411_ = lean_ctor_get(v_a_2407_, 0);
lean_inc(v_val_2411_);
lean_dec_ref(v_a_2407_);
v___x_2412_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2411_, v_a_2400_);
return v___x_2412_;
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
lean_dec(v_a_2407_);
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v_a_2400_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2414_);
v___x_2416_ = v___x_2409_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec_ref(v_a_2400_);
v_a_2419_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2406_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2406_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat___boxed(lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec_ref(v_a_2427_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(v_a_2435_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2454_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2454_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2454_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
if (lean_obj_tag(v_a_2443_) == 1)
{
lean_object* v_val_2447_; lean_object* v___x_2448_; 
lean_del_object(v___x_2445_);
v_val_2447_ = lean_ctor_get(v_a_2443_, 0);
lean_inc(v_val_2447_);
lean_dec_ref(v_a_2443_);
v___x_2448_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2447_, v_a_2436_);
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
lean_dec(v_a_2443_);
v___x_2449_ = lean_box(0);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
lean_ctor_set(v___x_2450_, 1, v_a_2436_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2450_);
v___x_2452_ = v___x_2445_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec_ref(v_a_2436_);
v_a_2455_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2442_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2442_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing___boxed(lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec_ref(v_a_2463_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; 
lean_inc_ref(v_a_2471_);
v___x_2478_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_a_2471_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2490_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2490_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2490_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
if (lean_obj_tag(v_a_2479_) == 1)
{
lean_object* v_val_2483_; lean_object* v___x_2484_; 
lean_del_object(v___x_2481_);
v_val_2483_ = lean_ctor_get(v_a_2479_, 0);
lean_inc(v_val_2483_);
lean_dec_ref(v_a_2479_);
v___x_2484_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2483_, v_a_2472_);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
lean_dec(v_a_2479_);
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v_a_2472_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2486_);
v___x_2488_ = v___x_2481_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_a_2472_);
v_a_2491_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2478_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2478_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith___boxed(lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec_ref(v_a_2499_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_Meta_Grind_AC_pp_x3f(v_a_2507_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2526_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2526_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2526_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
if (lean_obj_tag(v_a_2515_) == 1)
{
lean_object* v_val_2519_; lean_object* v___x_2520_; 
lean_del_object(v___x_2517_);
v_val_2519_ = lean_ctor_get(v_a_2515_, 0);
lean_inc(v_val_2519_);
lean_dec_ref(v_a_2515_);
v___x_2520_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2519_, v_a_2508_);
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
lean_dec(v_a_2515_);
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v_a_2508_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___x_2522_);
v___x_2524_ = v___x_2517_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec_ref(v_a_2508_);
v_a_2527_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2514_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2514_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC___boxed(lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec_ref(v_a_2535_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(lean_object* v_a_2543_, lean_object* v_as_2544_, size_t v_i_2545_, size_t v_stop_2546_, lean_object* v_b_2547_){
_start:
{
lean_object* v___y_2549_; uint8_t v___x_2553_; 
v___x_2553_ = lean_usize_dec_eq(v_i_2545_, v_stop_2546_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_array_uget_borrowed(v_as_2544_, v_i_2545_);
lean_inc_ref(v_a_2543_);
v___x_2555_ = l_Lean_Meta_Grind_Goal_getENode_x3f(v_a_2543_, v___x_2554_);
if (lean_obj_tag(v___x_2555_) == 1)
{
lean_object* v_val_2556_; lean_object* v_generation_2557_; uint8_t v___x_2558_; 
v_val_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_val_2556_);
lean_dec_ref(v___x_2555_);
v_generation_2557_ = lean_ctor_get(v_val_2556_, 8);
lean_inc(v_generation_2557_);
lean_dec(v_val_2556_);
v___x_2558_ = lean_nat_dec_le(v_b_2547_, v_generation_2557_);
if (v___x_2558_ == 0)
{
lean_dec(v_generation_2557_);
v___y_2549_ = v_b_2547_;
goto v___jp_2548_;
}
else
{
lean_dec(v_b_2547_);
v___y_2549_ = v_generation_2557_;
goto v___jp_2548_;
}
}
else
{
lean_dec(v___x_2555_);
v___y_2549_ = v_b_2547_;
goto v___jp_2548_;
}
}
else
{
return v_b_2547_;
}
v___jp_2548_:
{
size_t v___x_2550_; size_t v___x_2551_; 
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_add(v_i_2545_, v___x_2550_);
v_i_2545_ = v___x_2551_;
v_b_2547_ = v___y_2549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1___boxed(lean_object* v_a_2559_, lean_object* v_as_2560_, lean_object* v_i_2561_, lean_object* v_stop_2562_, lean_object* v_b_2563_){
_start:
{
size_t v_i_boxed_2564_; size_t v_stop_boxed_2565_; lean_object* v_res_2566_; 
v_i_boxed_2564_ = lean_unbox_usize(v_i_2561_);
lean_dec(v_i_2561_);
v_stop_boxed_2565_ = lean_unbox_usize(v_stop_2562_);
lean_dec(v_stop_2562_);
v_res_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2559_, v_as_2560_, v_i_boxed_2564_, v_stop_boxed_2565_, v_b_2563_);
lean_dec_ref(v_as_2560_);
lean_dec_ref(v_a_2559_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(lean_object* v_a_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_){
_start:
{
if (lean_obj_tag(v_x_2568_) == 0)
{
lean_object* v_cs_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_cs_2570_ = lean_ctor_get(v_x_2568_, 0);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = lean_array_get_size(v_cs_2570_);
v___x_2573_ = lean_nat_dec_lt(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
return v_x_2569_;
}
else
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_nat_dec_le(v___x_2572_, v___x_2572_);
if (v___x_2574_ == 0)
{
if (v___x_2573_ == 0)
{
return v_x_2569_;
}
else
{
size_t v___x_2575_; size_t v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = lean_usize_of_nat(v___x_2572_);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2567_, v_cs_2570_, v___x_2575_, v___x_2576_, v_x_2569_);
return v___x_2577_;
}
}
else
{
size_t v___x_2578_; size_t v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = lean_usize_of_nat(v___x_2572_);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2567_, v_cs_2570_, v___x_2578_, v___x_2579_, v_x_2569_);
return v___x_2580_;
}
}
}
else
{
lean_object* v_vs_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_vs_2581_ = lean_ctor_get(v_x_2568_, 0);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = lean_array_get_size(v_vs_2581_);
v___x_2584_ = lean_nat_dec_lt(v___x_2582_, v___x_2583_);
if (v___x_2584_ == 0)
{
return v_x_2569_;
}
else
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_nat_dec_le(v___x_2583_, v___x_2583_);
if (v___x_2585_ == 0)
{
if (v___x_2584_ == 0)
{
return v_x_2569_;
}
else
{
size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = ((size_t)0ULL);
v___x_2587_ = lean_usize_of_nat(v___x_2583_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2567_, v_vs_2581_, v___x_2586_, v___x_2587_, v_x_2569_);
return v___x_2588_;
}
}
else
{
size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = lean_usize_of_nat(v___x_2583_);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2567_, v_vs_2581_, v___x_2589_, v___x_2590_, v_x_2569_);
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(lean_object* v_a_2592_, lean_object* v_as_2593_, size_t v_i_2594_, size_t v_stop_2595_, lean_object* v_b_2596_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = lean_usize_dec_eq(v_i_2594_, v_stop_2595_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; size_t v___x_2600_; size_t v___x_2601_; 
v___x_2598_ = lean_array_uget_borrowed(v_as_2593_, v_i_2594_);
v___x_2599_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2592_, v___x_2598_, v_b_2596_);
v___x_2600_ = ((size_t)1ULL);
v___x_2601_ = lean_usize_add(v_i_2594_, v___x_2600_);
v_i_2594_ = v___x_2601_;
v_b_2596_ = v___x_2599_;
goto _start;
}
else
{
return v_b_2596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1___boxed(lean_object* v_a_2603_, lean_object* v_as_2604_, lean_object* v_i_2605_, lean_object* v_stop_2606_, lean_object* v_b_2607_){
_start:
{
size_t v_i_boxed_2608_; size_t v_stop_boxed_2609_; lean_object* v_res_2610_; 
v_i_boxed_2608_ = lean_unbox_usize(v_i_2605_);
lean_dec(v_i_2605_);
v_stop_boxed_2609_ = lean_unbox_usize(v_stop_2606_);
lean_dec(v_stop_2606_);
v_res_2610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2603_, v_as_2604_, v_i_boxed_2608_, v_stop_boxed_2609_, v_b_2607_);
lean_dec_ref(v_as_2604_);
lean_dec_ref(v_a_2603_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2___boxed(lean_object* v_a_2611_, lean_object* v_x_2612_, lean_object* v_x_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2611_, v_x_2612_, v_x_2613_);
lean_dec_ref(v_x_2612_);
lean_dec_ref(v_a_2611_);
return v_res_2614_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(lean_object* v_a_2616_, lean_object* v_x_2617_, size_t v_x_2618_, size_t v_x_2619_, lean_object* v_x_2620_){
_start:
{
if (lean_obj_tag(v_x_2617_) == 0)
{
lean_object* v_cs_2621_; lean_object* v___x_2622_; size_t v___x_2623_; lean_object* v_j_2624_; lean_object* v___x_2625_; size_t v___x_2626_; size_t v___x_2627_; size_t v___x_2628_; size_t v___x_2629_; size_t v___x_2630_; size_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v_cs_2621_ = lean_ctor_get(v_x_2617_, 0);
v___x_2622_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0);
v___x_2623_ = lean_usize_shift_right(v_x_2618_, v_x_2619_);
v_j_2624_ = lean_usize_to_nat(v___x_2623_);
v___x_2625_ = lean_array_get_borrowed(v___x_2622_, v_cs_2621_, v_j_2624_);
v___x_2626_ = ((size_t)1ULL);
v___x_2627_ = lean_usize_shift_left(v___x_2626_, v_x_2619_);
v___x_2628_ = lean_usize_sub(v___x_2627_, v___x_2626_);
v___x_2629_ = lean_usize_land(v_x_2618_, v___x_2628_);
v___x_2630_ = ((size_t)5ULL);
v___x_2631_ = lean_usize_sub(v_x_2619_, v___x_2630_);
v___x_2632_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2616_, v___x_2625_, v___x_2629_, v___x_2631_, v_x_2620_);
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_nat_add(v_j_2624_, v___x_2633_);
lean_dec(v_j_2624_);
v___x_2635_ = lean_array_get_size(v_cs_2621_);
v___x_2636_ = lean_nat_dec_lt(v___x_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_dec(v___x_2634_);
return v___x_2632_;
}
else
{
uint8_t v___x_2637_; 
v___x_2637_ = lean_nat_dec_le(v___x_2635_, v___x_2635_);
if (v___x_2637_ == 0)
{
if (v___x_2636_ == 0)
{
lean_dec(v___x_2634_);
return v___x_2632_;
}
else
{
size_t v___x_2638_; size_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_usize_of_nat(v___x_2634_);
lean_dec(v___x_2634_);
v___x_2639_ = lean_usize_of_nat(v___x_2635_);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2616_, v_cs_2621_, v___x_2638_, v___x_2639_, v___x_2632_);
return v___x_2640_;
}
}
else
{
size_t v___x_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_usize_of_nat(v___x_2634_);
lean_dec(v___x_2634_);
v___x_2642_ = lean_usize_of_nat(v___x_2635_);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2616_, v_cs_2621_, v___x_2641_, v___x_2642_, v___x_2632_);
return v___x_2643_;
}
}
}
else
{
lean_object* v_vs_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v_vs_2644_ = lean_ctor_get(v_x_2617_, 0);
v___x_2645_ = lean_usize_to_nat(v_x_2618_);
v___x_2646_ = lean_array_get_size(v_vs_2644_);
v___x_2647_ = lean_nat_dec_lt(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_dec(v___x_2645_);
return v_x_2620_;
}
else
{
uint8_t v___x_2648_; 
v___x_2648_ = lean_nat_dec_le(v___x_2646_, v___x_2646_);
if (v___x_2648_ == 0)
{
if (v___x_2647_ == 0)
{
lean_dec(v___x_2645_);
return v_x_2620_;
}
else
{
size_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = lean_usize_of_nat(v___x_2645_);
lean_dec(v___x_2645_);
v___x_2650_ = lean_usize_of_nat(v___x_2646_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2616_, v_vs_2644_, v___x_2649_, v___x_2650_, v_x_2620_);
return v___x_2651_;
}
}
else
{
size_t v___x_2652_; size_t v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = lean_usize_of_nat(v___x_2645_);
lean_dec(v___x_2645_);
v___x_2653_ = lean_usize_of_nat(v___x_2646_);
v___x_2654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2616_, v_vs_2644_, v___x_2652_, v___x_2653_, v_x_2620_);
return v___x_2654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___boxed(lean_object* v_a_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_){
_start:
{
size_t v_x_5390__boxed_2660_; size_t v_x_5391__boxed_2661_; lean_object* v_res_2662_; 
v_x_5390__boxed_2660_ = lean_unbox_usize(v_x_2657_);
lean_dec(v_x_2657_);
v_x_5391__boxed_2661_ = lean_unbox_usize(v_x_2658_);
lean_dec(v_x_2658_);
v_res_2662_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2655_, v_x_2656_, v_x_5390__boxed_2660_, v_x_5391__boxed_2661_, v_x_2659_);
lean_dec_ref(v_x_2656_);
lean_dec_ref(v_a_2655_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(lean_object* v_a_2663_, lean_object* v_t_2664_, lean_object* v_init_2665_, lean_object* v_start_2666_){
_start:
{
lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = lean_unsigned_to_nat(0u);
v___x_2668_ = lean_nat_dec_eq(v_start_2666_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v_root_2669_; lean_object* v_tail_2670_; size_t v_shift_2671_; lean_object* v_tailOff_2672_; uint8_t v___x_2673_; 
v_root_2669_ = lean_ctor_get(v_t_2664_, 0);
v_tail_2670_ = lean_ctor_get(v_t_2664_, 1);
v_shift_2671_ = lean_ctor_get_usize(v_t_2664_, 4);
v_tailOff_2672_ = lean_ctor_get(v_t_2664_, 3);
v___x_2673_ = lean_nat_dec_le(v_tailOff_2672_, v_start_2666_);
if (v___x_2673_ == 0)
{
size_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2674_ = lean_usize_of_nat(v_start_2666_);
v___x_2675_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2663_, v_root_2669_, v___x_2674_, v_shift_2671_, v_init_2665_);
v___x_2676_ = lean_array_get_size(v_tail_2670_);
v___x_2677_ = lean_nat_dec_lt(v___x_2667_, v___x_2676_);
if (v___x_2677_ == 0)
{
return v___x_2675_;
}
else
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_nat_dec_le(v___x_2676_, v___x_2676_);
if (v___x_2678_ == 0)
{
if (v___x_2677_ == 0)
{
return v___x_2675_;
}
else
{
size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2676_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2663_, v_tail_2670_, v___x_2679_, v___x_2680_, v___x_2675_);
return v___x_2681_;
}
}
else
{
size_t v___x_2682_; size_t v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = ((size_t)0ULL);
v___x_2683_ = lean_usize_of_nat(v___x_2676_);
v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2663_, v_tail_2670_, v___x_2682_, v___x_2683_, v___x_2675_);
return v___x_2684_;
}
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = lean_nat_sub(v_start_2666_, v_tailOff_2672_);
v___x_2686_ = lean_array_get_size(v_tail_2670_);
v___x_2687_ = lean_nat_dec_lt(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_dec(v___x_2685_);
return v_init_2665_;
}
else
{
uint8_t v___x_2688_; 
v___x_2688_ = lean_nat_dec_le(v___x_2686_, v___x_2686_);
if (v___x_2688_ == 0)
{
if (v___x_2687_ == 0)
{
lean_dec(v___x_2685_);
return v_init_2665_;
}
else
{
size_t v___x_2689_; size_t v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = lean_usize_of_nat(v___x_2685_);
lean_dec(v___x_2685_);
v___x_2690_ = lean_usize_of_nat(v___x_2686_);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2663_, v_tail_2670_, v___x_2689_, v___x_2690_, v_init_2665_);
return v___x_2691_;
}
}
else
{
size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = lean_usize_of_nat(v___x_2685_);
lean_dec(v___x_2685_);
v___x_2693_ = lean_usize_of_nat(v___x_2686_);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2663_, v_tail_2670_, v___x_2692_, v___x_2693_, v_init_2665_);
return v___x_2694_;
}
}
}
}
else
{
lean_object* v_root_2695_; lean_object* v_tail_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v_root_2695_ = lean_ctor_get(v_t_2664_, 0);
v_tail_2696_ = lean_ctor_get(v_t_2664_, 1);
v___x_2697_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2663_, v_root_2695_, v_init_2665_);
v___x_2698_ = lean_array_get_size(v_tail_2696_);
v___x_2699_ = lean_nat_dec_lt(v___x_2667_, v___x_2698_);
if (v___x_2699_ == 0)
{
return v___x_2697_;
}
else
{
uint8_t v___x_2700_; 
v___x_2700_ = lean_nat_dec_le(v___x_2698_, v___x_2698_);
if (v___x_2700_ == 0)
{
if (v___x_2699_ == 0)
{
return v___x_2697_;
}
else
{
size_t v___x_2701_; size_t v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((size_t)0ULL);
v___x_2702_ = lean_usize_of_nat(v___x_2698_);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2663_, v_tail_2696_, v___x_2701_, v___x_2702_, v___x_2697_);
return v___x_2703_;
}
}
else
{
size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = lean_usize_of_nat(v___x_2698_);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2663_, v_tail_2696_, v___x_2704_, v___x_2705_, v___x_2697_);
return v___x_2706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0___boxed(lean_object* v_a_2707_, lean_object* v_t_2708_, lean_object* v_init_2709_, lean_object* v_start_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_2707_, v_t_2708_, v_init_2709_, v_start_2710_);
lean_dec(v_start_2710_);
lean_dec_ref(v_t_2708_);
lean_dec_ref(v_a_2707_);
return v_res_2711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2(void){
_start:
{
lean_object* v___x_2715_; uint8_t v___x_2716_; double v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2715_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2716_ = 1;
v___x_2717_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2718_ = lean_box(0);
v___x_2719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1));
v___x_2720_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___x_2718_);
lean_ctor_set(v___x_2720_, 2, v___x_2715_);
lean_ctor_set_float(v___x_2720_, sizeof(void*)*3, v___x_2717_);
lean_ctor_set_float(v___x_2720_, sizeof(void*)*3 + 8, v___x_2717_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*3 + 16, v___x_2716_);
return v___x_2720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4));
v___x_2725_ = l_Lean_MessageData_ofFormat(v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8));
v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
return v___x_2731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10));
v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
return v___x_2734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12));
v___x_2737_ = l_Lean_stringToMessageData(v___x_2736_);
return v___x_2737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14));
v___x_2740_ = l_Lean_stringToMessageData(v___x_2739_);
return v___x_2740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17(void){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16));
v___x_2743_ = l_Lean_stringToMessageData(v___x_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(lean_object* v_c_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_toGoalState_2749_; lean_object* v_exprs_2750_; lean_object* v_ematch_2751_; lean_object* v_split_2752_; lean_object* v___x_2753_; lean_object* v_msgs_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___x_2788_; lean_object* v_splits_2789_; lean_object* v_ematch_2790_; lean_object* v_gen_2791_; lean_object* v_instances_2792_; lean_object* v_numInstances_2793_; lean_object* v_num_2794_; lean_object* v___x_2795_; lean_object* v_msgs_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v_msgs_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v_msgs_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; uint8_t v___x_2854_; 
v_toGoalState_2749_ = lean_ctor_get(v_a_2745_, 0);
v_exprs_2750_ = lean_ctor_get(v_toGoalState_2749_, 2);
v_ematch_2751_ = lean_ctor_get(v_toGoalState_2749_, 12);
v_split_2752_ = lean_ctor_get(v_toGoalState_2749_, 14);
v___x_2753_ = lean_unsigned_to_nat(0u);
v___x_2788_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_2745_, v_exprs_2750_, v___x_2753_, v___x_2753_);
v_splits_2789_ = lean_ctor_get(v_c_2744_, 0);
v_ematch_2790_ = lean_ctor_get(v_c_2744_, 1);
v_gen_2791_ = lean_ctor_get(v_c_2744_, 2);
v_instances_2792_ = lean_ctor_get(v_c_2744_, 3);
v_numInstances_2793_ = lean_ctor_get(v_ematch_2751_, 4);
v_num_2794_ = lean_ctor_get(v_ematch_2751_, 6);
v___x_2795_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2854_ = lean_nat_dec_le(v_instances_2792_, v_numInstances_2793_);
if (v___x_2854_ == 0)
{
v_msgs_2836_ = v___x_2795_;
v___y_2837_ = v_a_2746_;
v___y_2838_ = v_a_2747_;
goto v___jp_2835_;
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; double v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2858_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2859_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2859_, 0, v___x_2855_);
lean_ctor_set(v___x_2859_, 1, v___x_2856_);
lean_ctor_set(v___x_2859_, 2, v___x_2858_);
lean_ctor_set_float(v___x_2859_, sizeof(void*)*3, v___x_2857_);
lean_ctor_set_float(v___x_2859_, sizeof(void*)*3 + 8, v___x_2857_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*3 + 16, v___x_2854_);
v___x_2860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17);
lean_inc(v_instances_2792_);
v___x_2861_ = l_Nat_reprFast(v_instances_2792_);
v___x_2862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
v___x_2863_ = l_Lean_MessageData_ofFormat(v___x_2862_);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2860_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2859_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
lean_ctor_set(v___x_2867_, 2, v___x_2795_);
v___x_2868_ = lean_array_push(v___x_2795_, v___x_2867_);
v_msgs_2836_ = v___x_2868_;
v___y_2837_ = v_a_2746_;
v___y_2838_ = v_a_2747_;
goto v___jp_2835_;
}
v___jp_2754_:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(v_a_2745_, v_c_2744_, v_msgs_2755_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2774_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2774_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2774_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = lean_array_get_size(v_a_2759_);
v___x_2764_ = lean_nat_dec_eq(v___x_2763_, v___x_2753_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_del_object(v___x_2761_);
v___x_2765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2);
v___x_2766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5);
v___x_2767_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
lean_ctor_set(v___x_2767_, 2, v_a_2759_);
v___x_2768_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2767_, v___y_2756_);
return v___x_2768_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_a_2759_);
v___x_2769_ = lean_box(0);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v___y_2756_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2770_);
v___x_2772_ = v___x_2761_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref(v___y_2756_);
v_a_2775_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2777_ = v___x_2758_;
v_isShared_2778_ = v_isSharedCheck_2787_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2758_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2787_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v_ref_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v_ref_2779_ = lean_ctor_get(v___y_2757_, 5);
v___x_2780_ = lean_io_error_to_string(v_a_2775_);
v___x_2781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
v___x_2782_ = l_Lean_MessageData_ofFormat(v___x_2781_);
lean_inc(v_ref_2779_);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_ref_2779_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2783_);
v___x_2785_ = v___x_2777_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
v___jp_2796_:
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_nat_dec_le(v_gen_2791_, v___x_2788_);
lean_dec(v___x_2788_);
if (v___x_2800_ == 0)
{
v_msgs_2755_ = v_msgs_2797_;
v___y_2756_ = v___y_2798_;
v___y_2757_ = v___y_2799_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; double v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2804_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2805_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2805_, 0, v___x_2801_);
lean_ctor_set(v___x_2805_, 1, v___x_2802_);
lean_ctor_set(v___x_2805_, 2, v___x_2804_);
lean_ctor_set_float(v___x_2805_, sizeof(void*)*3, v___x_2803_);
lean_ctor_set_float(v___x_2805_, sizeof(void*)*3 + 8, v___x_2803_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*3 + 16, v___x_2800_);
v___x_2806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9);
lean_inc(v_gen_2791_);
v___x_2807_ = l_Nat_reprFast(v_gen_2791_);
v___x_2808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = l_Lean_MessageData_ofFormat(v___x_2808_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2806_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2805_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
lean_ctor_set(v___x_2813_, 2, v___x_2795_);
v___x_2814_ = lean_array_push(v_msgs_2797_, v___x_2813_);
v_msgs_2755_ = v___x_2814_;
v___y_2756_ = v___y_2798_;
v___y_2757_ = v___y_2799_;
goto v___jp_2754_;
}
}
v___jp_2815_:
{
lean_object* v_num_2819_; uint8_t v___x_2820_; 
v_num_2819_ = lean_ctor_get(v_split_2752_, 0);
v___x_2820_ = lean_nat_dec_le(v_splits_2789_, v_num_2819_);
if (v___x_2820_ == 0)
{
v_msgs_2797_ = v_msgs_2816_;
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2818_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; double v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2824_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2825_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2825_, 0, v___x_2821_);
lean_ctor_set(v___x_2825_, 1, v___x_2822_);
lean_ctor_set(v___x_2825_, 2, v___x_2824_);
lean_ctor_set_float(v___x_2825_, sizeof(void*)*3, v___x_2823_);
lean_ctor_set_float(v___x_2825_, sizeof(void*)*3 + 8, v___x_2823_);
lean_ctor_set_uint8(v___x_2825_, sizeof(void*)*3 + 16, v___x_2820_);
v___x_2826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13);
lean_inc(v_splits_2789_);
v___x_2827_ = l_Nat_reprFast(v_splits_2789_);
v___x_2828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
v___x_2829_ = l_Lean_MessageData_ofFormat(v___x_2828_);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2826_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v___x_2831_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2825_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
lean_ctor_set(v___x_2833_, 2, v___x_2795_);
v___x_2834_ = lean_array_push(v_msgs_2816_, v___x_2833_);
v_msgs_2797_ = v___x_2834_;
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2818_;
goto v___jp_2796_;
}
}
v___jp_2835_:
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_nat_dec_le(v_ematch_2790_, v_num_2794_);
if (v___x_2839_ == 0)
{
v_msgs_2816_ = v_msgs_2836_;
v___y_2817_ = v___y_2837_;
v___y_2818_ = v___y_2838_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; double v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2843_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2844_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2844_, 0, v___x_2840_);
lean_ctor_set(v___x_2844_, 1, v___x_2841_);
lean_ctor_set(v___x_2844_, 2, v___x_2843_);
lean_ctor_set_float(v___x_2844_, sizeof(void*)*3, v___x_2842_);
lean_ctor_set_float(v___x_2844_, sizeof(void*)*3 + 8, v___x_2842_);
lean_ctor_set_uint8(v___x_2844_, sizeof(void*)*3 + 16, v___x_2839_);
v___x_2845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15);
lean_inc(v_ematch_2790_);
v___x_2846_ = l_Nat_reprFast(v_ematch_2790_);
v___x_2847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
v___x_2848_ = l_Lean_MessageData_ofFormat(v___x_2847_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2845_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2844_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
lean_ctor_set(v___x_2852_, 2, v___x_2795_);
v___x_2853_ = lean_array_push(v_msgs_2836_, v___x_2852_);
v_msgs_2816_ = v___x_2853_;
v___y_2817_ = v___y_2837_;
v___y_2818_ = v___y_2838_;
goto v___jp_2815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___boxed(lean_object* v_c_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_c_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
lean_dec_ref(v_a_2872_);
lean_dec_ref(v_a_2870_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(lean_object* v_c_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_c_2875_, v_a_2876_, v_a_2877_, v_a_2880_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___boxed(lean_object* v_c_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(v_c_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec_ref(v_a_2885_);
return v_res_2892_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2896_; uint8_t v___x_2897_; double v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2896_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2897_ = 1;
v___x_2898_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2899_ = lean_box(0);
v___x_2900_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1));
v___x_2901_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
lean_ctor_set(v___x_2901_, 1, v___x_2899_);
lean_ctor_set(v___x_2901_, 2, v___x_2896_);
lean_ctor_set_float(v___x_2901_, sizeof(void*)*3, v___x_2898_);
lean_ctor_set_float(v___x_2901_, sizeof(void*)*3 + 8, v___x_2898_);
lean_ctor_set_uint8(v___x_2901_, sizeof(void*)*3 + 16, v___x_2897_);
return v___x_2901_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3));
v___x_2904_ = l_Lean_stringToMessageData(v___x_2903_);
return v___x_2904_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2));
v___x_2906_ = l_Lean_stringToMessageData(v___x_2905_);
return v___x_2906_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6));
v___x_2909_ = l_Lean_stringToMessageData(v___x_2908_);
return v___x_2909_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8));
v___x_2912_ = l_Lean_stringToMessageData(v___x_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(lean_object* v_as_x27_2913_, lean_object* v_b_2914_, lean_object* v___y_2915_){
_start:
{
if (lean_obj_tag(v_as_x27_2913_) == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v_b_2914_);
lean_ctor_set(v___x_2917_, 1, v___y_2915_);
v___x_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
return v___x_2918_;
}
else
{
lean_object* v_head_2919_; lean_object* v_tail_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2958_; 
v_head_2919_ = lean_ctor_get(v_as_x27_2913_, 0);
v_tail_2920_ = lean_ctor_get(v_as_x27_2913_, 1);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_as_x27_2913_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2922_ = v_as_x27_2913_;
v_isShared_2923_ = v_isSharedCheck_2958_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_tail_2920_);
lean_inc(v_head_2919_);
lean_dec(v_as_x27_2913_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2958_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v_expr_2924_; lean_object* v_i_2925_; lean_object* v_num_2926_; lean_object* v_source_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v_expr_2924_ = lean_ctor_get(v_head_2919_, 0);
lean_inc_ref(v_expr_2924_);
v_i_2925_ = lean_ctor_get(v_head_2919_, 1);
lean_inc(v_i_2925_);
v_num_2926_ = lean_ctor_get(v_head_2919_, 2);
lean_inc(v_num_2926_);
v_source_2927_ = lean_ctor_get(v_head_2919_, 3);
lean_inc(v_source_2927_);
lean_dec(v_head_2919_);
v___x_2928_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2929_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
v___x_2930_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4);
v___x_2931_ = lean_unsigned_to_nat(1u);
v___x_2932_ = lean_nat_add(v_i_2925_, v___x_2931_);
lean_dec(v_i_2925_);
v___x_2933_ = l_Nat_reprFast(v___x_2932_);
v___x_2934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
v___x_2935_ = l_Lean_MessageData_ofFormat(v___x_2934_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set_tag(v___x_2922_, 7);
lean_ctor_set(v___x_2922_, 1, v___x_2935_);
lean_ctor_set(v___x_2922_, 0, v___x_2930_);
v___x_2937_ = v___x_2922_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2938_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5);
v___x_2939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = l_Nat_reprFast(v_num_2926_);
v___x_2941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
v___x_2942_ = l_Lean_MessageData_ofFormat(v___x_2941_);
v___x_2943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2939_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7);
v___x_2945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = l_Lean_MessageData_ofExpr(v_expr_2924_);
v___x_2947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9);
v___x_2949_ = l_Lean_Meta_Grind_SplitSource_toMessageData(v_source_2927_);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2929_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
lean_ctor_set(v___x_2951_, 2, v___x_2928_);
v___x_2952_ = lean_mk_empty_array_with_capacity(v___x_2931_);
v___x_2953_ = lean_array_push(v___x_2952_, v___x_2951_);
v___x_2954_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2929_);
lean_ctor_set(v___x_2954_, 1, v___x_2947_);
lean_ctor_set(v___x_2954_, 2, v___x_2953_);
v___x_2955_ = lean_array_push(v_b_2914_, v___x_2954_);
v_as_x27_2913_ = v_tail_2920_;
v_b_2914_ = v___x_2955_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___boxed(lean_object* v_as_x27_2959_, lean_object* v_b_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_2959_, v_b_2960_, v___y_2961_);
return v_res_2963_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1));
v___x_2968_ = l_Lean_MessageData_ofFormat(v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v_toGoalState_2976_; lean_object* v_split_2977_; lean_object* v_trace_2978_; uint8_t v___x_2979_; 
v_toGoalState_2976_ = lean_ctor_get(v_a_2969_, 0);
v_split_2977_ = lean_ctor_get(v_toGoalState_2976_, 14);
v_trace_2978_ = lean_ctor_get(v_split_2977_, 4);
v___x_2979_ = l_List_isEmpty___redArg(v_trace_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v_a_2983_; lean_object* v_fst_2984_; lean_object* v_snd_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2980_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
lean_inc(v_trace_2978_);
v___x_2981_ = l_List_reverse___redArg(v_trace_2978_);
v___x_2982_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v___x_2981_, v___x_2980_, v_a_2970_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
v_fst_2984_ = lean_ctor_get(v_a_2983_, 0);
lean_inc(v_fst_2984_);
v_snd_2985_ = lean_ctor_get(v_a_2983_, 1);
lean_inc(v_snd_2985_);
lean_dec(v_a_2983_);
v___x_2986_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
v___x_2987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2);
v___x_2988_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
lean_ctor_set(v___x_2988_, 2, v_fst_2984_);
v___x_2989_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2988_, v_snd_2985_);
return v___x_2989_;
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_box(0);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v_a_2970_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___boxed(lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec_ref(v_a_2993_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(lean_object* v_as_3001_, lean_object* v_as_x27_3002_, lean_object* v_b_3003_, lean_object* v_a_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_3002_, v_b_3003_, v___y_3006_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___boxed(lean_object* v_as_3013_, lean_object* v_as_x27_3014_, lean_object* v_b_3015_, lean_object* v_a_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(v_as_3013_, v_as_x27_3014_, v_b_3015_, v_a_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec_ref(v___y_3017_);
lean_dec(v_as_3013_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(lean_object* v_goal_3029_, lean_object* v_config_3030_, uint8_t v_collapsedMain_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_toGoalState_3039_; lean_object* v_facts_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v_a_3047_; lean_object* v_snd_3048_; lean_object* v___x_3049_; 
v_toGoalState_3039_ = lean_ctor_get(v_goal_3029_, 0);
v_facts_3040_ = lean_ctor_get(v_toGoalState_3039_, 10);
v___x_3041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1));
v___x_3042_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2));
v___x_3043_ = l_Lean_PersistentArray_toArray___redArg(v_facts_3040_);
v___x_3044_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4___redArg___closed__4));
v___x_3045_ = l_Lean_Meta_Grind_ppExprArray(v___x_3041_, v___x_3042_, v___x_3043_, v___x_3044_, v_collapsedMain_3031_);
v___x_3046_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_3045_, v_a_3033_);
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
v_snd_3048_ = lean_ctor_get(v_a_3047_, 1);
lean_inc(v_snd_3048_);
lean_dec(v_a_3047_);
v___x_3049_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(v_collapsedMain_3031_, v_a_3032_, v_snd_3048_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v_snd_3051_; lean_object* v___x_3052_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref(v___x_3049_);
v_snd_3051_ = lean_ctor_get(v_a_3050_, 1);
lean_inc(v_snd_3051_);
lean_dec(v_a_3050_);
v___x_3052_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(v_a_3032_, v_snd_3051_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v_snd_3054_; lean_object* v___x_3055_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
v_snd_3054_ = lean_ctor_get(v_a_3053_, 1);
lean_inc(v_snd_3054_);
lean_dec(v_a_3053_);
v___x_3055_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(v_a_3032_, v_snd_3054_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v_snd_3057_; lean_object* v___x_3058_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___x_3055_);
v_snd_3057_ = lean_ctor_get(v_a_3056_, 1);
lean_inc(v_snd_3057_);
lean_dec(v_a_3056_);
v___x_3058_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(v_a_3032_, v_snd_3057_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v_snd_3060_; lean_object* v___x_3061_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v_snd_3060_ = lean_ctor_get(v_a_3059_, 1);
lean_inc(v_snd_3060_);
lean_dec(v_a_3059_);
v___x_3061_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(v_a_3032_, v_snd_3060_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v_snd_3063_; lean_object* v___x_3064_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref(v___x_3061_);
v_snd_3063_ = lean_ctor_get(v_a_3062_, 1);
lean_inc(v_snd_3063_);
lean_dec(v_a_3062_);
v___x_3064_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(v_a_3032_, v_snd_3063_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v_snd_3066_; lean_object* v___x_3067_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref(v___x_3064_);
v_snd_3066_ = lean_ctor_get(v_a_3065_, 1);
lean_inc(v_snd_3066_);
lean_dec(v_a_3065_);
v___x_3067_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(v_a_3032_, v_snd_3066_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v_snd_3069_; lean_object* v___x_3070_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
v_snd_3069_ = lean_ctor_get(v_a_3068_, 1);
lean_inc(v_snd_3069_);
lean_dec(v_a_3068_);
v___x_3070_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_config_3030_, v_a_3032_, v_snd_3069_, v_a_3036_);
return v___x_3070_;
}
else
{
lean_dec_ref(v_config_3030_);
return v___x_3067_;
}
}
else
{
lean_dec_ref(v_config_3030_);
return v___x_3064_;
}
}
else
{
lean_dec_ref(v_config_3030_);
return v___x_3061_;
}
}
else
{
lean_dec_ref(v_config_3030_);
return v___x_3058_;
}
}
else
{
lean_dec_ref(v_config_3030_);
return v___x_3055_;
}
}
else
{
lean_dec_ref(v_config_3030_);
return v___x_3052_;
}
}
else
{
lean_dec_ref(v_config_3030_);
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___boxed(lean_object* v_goal_3071_, lean_object* v_config_3072_, lean_object* v_collapsedMain_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
uint8_t v_collapsedMain_boxed_3081_; lean_object* v_res_3082_; 
v_collapsedMain_boxed_3081_ = lean_unbox(v_collapsedMain_3073_);
v_res_3082_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_3071_, v_config_3072_, v_collapsedMain_boxed_3081_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec_ref(v_a_3074_);
lean_dec_ref(v_goal_3071_);
return v_res_3082_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2(void){
_start:
{
lean_object* v___x_3086_; uint8_t v___x_3087_; double v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3086_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_3087_ = 0;
v___x_3088_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_3089_ = lean_box(0);
v___x_3090_ = ((lean_object*)(l_Lean_Meta_Grind_goalDiagToMessageData___closed__1));
v___x_3091_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___x_3089_);
lean_ctor_set(v___x_3091_, 2, v___x_3086_);
lean_ctor_set_float(v___x_3091_, sizeof(void*)*3, v___x_3088_);
lean_ctor_set_float(v___x_3091_, sizeof(void*)*3 + 8, v___x_3088_);
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*3 + 16, v___x_3087_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData(lean_object* v_goal_3092_, lean_object* v_config_3093_, lean_object* v_header_3094_, uint8_t v_collapsedMain_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_3102_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_3092_, v_config_3093_, v_collapsedMain_3095_, v_goal_3092_, v___x_3101_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3115_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3115_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3115_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v_snd_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v_snd_3107_ = lean_ctor_get(v_a_3103_, 1);
lean_inc(v_snd_3107_);
lean_dec(v_a_3103_);
v___x_3108_ = lean_obj_once(&l_Lean_Meta_Grind_goalDiagToMessageData___closed__2, &l_Lean_Meta_Grind_goalDiagToMessageData___closed__2_once, _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2);
v___x_3109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3109_, 0, v_header_3094_);
v___x_3110_ = l_Lean_MessageData_ofFormat(v___x_3109_);
v___x_3111_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3108_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
lean_ctor_set(v___x_3111_, 2, v_snd_3107_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3111_);
v___x_3113_ = v___x_3105_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec_ref(v_header_3094_);
v_a_3116_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3102_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3102_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___boxed(lean_object* v_goal_3124_, lean_object* v_config_3125_, lean_object* v_header_3126_, lean_object* v_collapsedMain_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
uint8_t v_collapsedMain_boxed_3133_; lean_object* v_res_3134_; 
v_collapsedMain_boxed_3133_ = lean_unbox(v_collapsedMain_3127_);
v_res_3134_ = l_Lean_Meta_Grind_goalDiagToMessageData(v_goal_3124_, v_config_3125_, v_header_3126_, v_collapsedMain_boxed_3133_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec_ref(v_goal_3124_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(lean_object* v_msgData_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; lean_object* v_env_3142_; lean_object* v___x_3143_; lean_object* v_mctx_3144_; lean_object* v_lctx_3145_; lean_object* v_options_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3141_ = lean_st_ref_get(v___y_3139_);
v_env_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc_ref(v_env_3142_);
lean_dec(v___x_3141_);
v___x_3143_ = lean_st_ref_get(v___y_3137_);
v_mctx_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc_ref(v_mctx_3144_);
lean_dec(v___x_3143_);
v_lctx_3145_ = lean_ctor_get(v___y_3136_, 2);
v_options_3146_ = lean_ctor_get(v___y_3138_, 2);
lean_inc_ref(v_options_3146_);
lean_inc_ref(v_lctx_3145_);
v___x_3147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3147_, 0, v_env_3142_);
lean_ctor_set(v___x_3147_, 1, v_mctx_3144_);
lean_ctor_set(v___x_3147_, 2, v_lctx_3145_);
lean_ctor_set(v___x_3147_, 3, v_options_3146_);
v___x_3148_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v_msgData_3135_);
v___x_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0___boxed(lean_object* v_msgData_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(v_msgData_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(lean_object* v_mvarId_3157_, lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3157_, v_x_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_a_3173_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3164_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3164_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg___boxed(lean_object* v_mvarId_3181_, lean_object* v_x_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3181_, v_x_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(lean_object* v_00_u03b1_3189_, lean_object* v_mvarId_3190_, lean_object* v_x_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3190_, v_x_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___boxed(lean_object* v_00_u03b1_3198_, lean_object* v_mvarId_3199_, lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(v_00_u03b1_3198_, v_mvarId_3199_, v_x_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
return v_res_3206_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0));
v___x_3209_ = l_Lean_stringToMessageData(v___x_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0(uint8_t v_verbose_3210_, lean_object* v_mvarId_3211_, lean_object* v_goal_3212_, lean_object* v_config_3213_, uint8_t v___x_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
if (v_verbose_3210_ == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec_ref(v_config_3213_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_mvarId_3211_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0));
v___x_3223_ = l_Lean_Meta_Grind_goalDiagToMessageData(v_goal_3212_, v_config_3213_, v___x_3222_, v___x_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3235_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3235_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3235_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set_tag(v___x_3226_, 1);
lean_ctor_set(v___x_3226_, 0, v_mvarId_3211_);
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_mvarId_3211_);
v___x_3229_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3230_ = lean_obj_once(&l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1, &l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3229_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v_a_3224_);
v___x_3233_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(v___x_3232_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
return v___x_3233_;
}
}
}
else
{
lean_dec(v_mvarId_3211_);
return v___x_3223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed(lean_object* v_verbose_3236_, lean_object* v_mvarId_3237_, lean_object* v_goal_3238_, lean_object* v_config_3239_, lean_object* v___x_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
uint8_t v_verbose_boxed_3246_; uint8_t v___x_1179__boxed_3247_; lean_object* v_res_3248_; 
v_verbose_boxed_3246_ = lean_unbox(v_verbose_3236_);
v___x_1179__boxed_3247_ = lean_unbox(v___x_3240_);
v_res_3248_ = l_Lean_Meta_Grind_goalToMessageData___lam__0(v_verbose_boxed_3246_, v_mvarId_3237_, v_goal_3238_, v_config_3239_, v___x_1179__boxed_3247_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec_ref(v_goal_3238_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object* v_goal_3249_, lean_object* v_config_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
uint8_t v_verbose_3256_; lean_object* v_mvarId_3257_; uint8_t v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___y_3261_; lean_object* v___x_3262_; 
v_verbose_3256_ = lean_ctor_get_uint8(v_config_3250_, sizeof(void*)*11 + 15);
v_mvarId_3257_ = lean_ctor_get(v_goal_3249_, 1);
lean_inc_n(v_mvarId_3257_, 2);
v___x_3258_ = 1;
v___x_3259_ = lean_box(v_verbose_3256_);
v___x_3260_ = lean_box(v___x_3258_);
v___y_3261_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed), 10, 5);
lean_closure_set(v___y_3261_, 0, v___x_3259_);
lean_closure_set(v___y_3261_, 1, v_mvarId_3257_);
lean_closure_set(v___y_3261_, 2, v_goal_3249_);
lean_closure_set(v___y_3261_, 3, v_config_3250_);
lean_closure_set(v___y_3261_, 4, v___x_3260_);
v___x_3262_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3257_, v___y_3261_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___boxed(lean_object* v_goal_3263_, lean_object* v_config_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Meta_Grind_goalToMessageData(v_goal_3263_, v_config_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
return v_res_3270_;
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
