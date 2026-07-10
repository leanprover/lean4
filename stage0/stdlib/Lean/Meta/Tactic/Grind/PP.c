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
uint8_t lean_bool_not(uint8_t);
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_197_; uint8_t v___y_199_; uint8_t v___x_224_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_224_ = l_Lean_Expr_isApp(v_e_190_);
if (v___x_224_ == 0)
{
lean_dec(v_a_197_);
v___y_199_ = v___x_224_;
goto v___jp_198_;
}
else
{
uint8_t v___x_225_; uint8_t v___x_226_; 
v___x_225_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
v___x_226_ = lean_bool_not(v___x_225_);
v___y_199_ = v___x_226_;
goto v___jp_198_;
}
v___jp_198_:
{
if (v___y_199_ == 0)
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_ppExpr(v_e_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_209_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_209_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = l_Lean_MessageData_ofFormat(v_a_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_205_);
v___x_207_ = v___x_203_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_200_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_200_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v_dummy_218_; lean_object* v_nargs_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_dummy_218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___closed__0);
v_nargs_219_ = l_Lean_Expr_getAppNumArgs(v_e_190_);
lean_inc(v_nargs_219_);
v___x_220_ = lean_mk_array(v_nargs_219_, v_dummy_218_);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_sub(v_nargs_219_, v___x_221_);
lean_dec(v_nargs_219_);
v___x_223_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue_spec__1(v_goal_189_, v_e_190_, v___x_220_, v___x_222_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
return v___x_223_;
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
lean_object* v_a_313_; lean_object* v_root_314_; uint8_t v_interpreted_315_; uint8_t v_ctor_316_; lean_object* v_r_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v_r_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
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
v___x_336_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_277_, v_root_314_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_276_, v_root_314_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
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
lean_dec_ref_known(v___x_335_, 2);
lean_dec_ref(v_e_277_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___boxed(lean_object* v_goal_350_, lean_object* v_e_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_350_, v_e_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec_ref(v_goal_350_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(lean_object* v_goal_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
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
v___x_373_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_358_, v_head_368_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
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
lean_dec_ref(v_goal_388_);
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
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v_b_419_);
return v___x_425_;
}
else
{
lean_object* v_head_426_; lean_object* v_tail_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_head_426_ = lean_ctor_get(v_as_x27_418_, 0);
v_tail_427_ = lean_ctor_get(v_as_x27_418_, 1);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = l_List_lengthTR___redArg(v_head_426_);
v___x_430_ = lean_nat_dec_lt(v___x_428_, v___x_429_);
lean_dec(v___x_429_);
if (v___x_430_ == 0)
{
v_as_x27_418_ = v_tail_427_;
goto _start;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_box(0);
lean_inc(v_head_426_);
v___x_433_ = l_List_mapM_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__0(v_goal_417_, v_head_426_, v___x_432_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v_b_419_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__8);
v___x_440_ = l_Lean_MessageData_joinSep(v_a_434_, v___x_439_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_438_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v_as_x27_418_ = v_tail_427_;
v_b_419_ = v___x_443_;
goto _start;
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v_b_419_);
v_a_445_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_433_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_433_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___boxed(lean_object* v_goal_453_, lean_object* v_as_x27_454_, lean_object* v_b_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_453_, v_as_x27_454_, v_b_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v_as_x27_454_);
lean_dec_ref(v_goal_453_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(lean_object* v_goal_462_, lean_object* v_as_463_, size_t v_sz_464_, size_t v_i_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = lean_usize_dec_lt(v_i_465_, v_sz_464_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v_b_466_);
return v___x_473_;
}
else
{
lean_object* v_snd_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_510_; 
v_snd_474_ = lean_ctor_get(v_b_466_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_b_466_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_b_466_, 0);
lean_dec(v_unused_511_);
v___x_476_ = v_b_466_;
v_isShared_477_ = v_isSharedCheck_510_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snd_474_);
lean_dec(v_b_466_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_510_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_array_uget_borrowed(v_as_463_, v_i_465_);
lean_inc(v_a_478_);
v___x_479_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_462_, v_a_478_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v_self_481_; lean_object* v___x_482_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v_self_481_ = lean_ctor_get(v_a_480_, 0);
lean_inc_ref(v_self_481_);
lean_dec(v_a_480_);
v___x_482_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_462_, v_self_481_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_box(0);
v___x_485_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v_snd_474_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_a_483_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_487_);
lean_ctor_set(v___x_476_, 0, v___x_484_);
v___x_489_ = v___x_476_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
size_t v___x_490_; size_t v___x_491_; 
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_465_, v___x_490_);
v_i_465_ = v___x_491_;
v_b_466_ = v___x_489_;
goto _start;
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_del_object(v___x_476_);
lean_dec(v_snd_474_);
v_a_494_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_482_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_del_object(v___x_476_);
lean_dec(v_snd_474_);
v_a_502_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_479_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_479_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_goal_512_, lean_object* v_as_513_, lean_object* v_sz_514_, lean_object* v_i_515_, lean_object* v_b_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
size_t v_sz_boxed_522_; size_t v_i_boxed_523_; lean_object* v_res_524_; 
v_sz_boxed_522_ = lean_unbox_usize(v_sz_514_);
lean_dec(v_sz_514_);
v_i_boxed_523_ = lean_unbox_usize(v_i_515_);
lean_dec(v_i_515_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(v_goal_512_, v_as_513_, v_sz_boxed_522_, v_i_boxed_523_, v_b_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v_as_513_);
lean_dec_ref(v_goal_512_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(lean_object* v_goal_525_, lean_object* v_as_526_, size_t v_sz_527_, size_t v_i_528_, lean_object* v_b_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = lean_usize_dec_lt(v_i_528_, v_sz_527_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v_b_529_);
return v___x_536_;
}
else
{
lean_object* v_snd_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_573_; 
v_snd_537_ = lean_ctor_get(v_b_529_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_b_529_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_b_529_, 0);
lean_dec(v_unused_574_);
v___x_539_ = v_b_529_;
v_isShared_540_ = v_isSharedCheck_573_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_537_);
lean_dec(v_b_529_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_573_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_array_uget_borrowed(v_as_526_, v_i_528_);
lean_inc(v_a_541_);
v___x_542_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_525_, v_a_541_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v_self_544_; lean_object* v___x_545_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v_self_544_ = lean_ctor_get(v_a_543_, 0);
lean_inc_ref(v_self_544_);
lean_dec(v_a_543_);
v___x_545_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_525_, v_self_544_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = lean_box(0);
v___x_548_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v_snd_537_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_a_546_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_550_);
lean_ctor_set(v___x_539_, 0, v___x_547_);
v___x_552_ = v___x_539_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; 
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_add(v_i_528_, v___x_553_);
v___x_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3_spec__5(v_goal_525_, v_as_526_, v_sz_527_, v___x_554_, v___x_552_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_555_;
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_del_object(v___x_539_);
lean_dec(v_snd_537_);
v_a_557_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_545_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_545_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_del_object(v___x_539_);
lean_dec(v_snd_537_);
v_a_565_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_542_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_542_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3___boxed(lean_object* v_goal_575_, lean_object* v_as_576_, lean_object* v_sz_577_, lean_object* v_i_578_, lean_object* v_b_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_577_);
lean_dec(v_sz_577_);
v_i_boxed_586_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(v_goal_575_, v_as_576_, v_sz_boxed_585_, v_i_boxed_586_, v_b_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v_as_576_);
lean_dec_ref(v_goal_575_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(lean_object* v_init_588_, lean_object* v_goal_589_, lean_object* v_n_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
if (lean_obj_tag(v_n_590_) == 0)
{
lean_object* v_cs_597_; lean_object* v___x_598_; lean_object* v___x_599_; size_t v_sz_600_; size_t v___x_601_; lean_object* v___x_602_; 
v_cs_597_ = lean_ctor_get(v_n_590_, 0);
v___x_598_ = lean_box(0);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v_b_591_);
v_sz_600_ = lean_array_size(v_cs_597_);
v___x_601_ = ((size_t)0ULL);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(v_init_588_, v_goal_589_, v_cs_597_, v_sz_600_, v___x_601_, v___x_599_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_617_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_617_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_617_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_617_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_fst_607_; 
v_fst_607_ = lean_ctor_get(v_a_603_, 0);
if (lean_obj_tag(v_fst_607_) == 0)
{
lean_object* v_snd_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v_snd_608_ = lean_ctor_get(v_a_603_, 1);
lean_inc(v_snd_608_);
lean_dec(v_a_603_);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v_snd_608_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_609_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
else
{
lean_object* v_val_613_; lean_object* v___x_615_; 
lean_inc_ref(v_fst_607_);
lean_dec(v_a_603_);
v_val_613_ = lean_ctor_get(v_fst_607_, 0);
lean_inc(v_val_613_);
lean_dec_ref_known(v_fst_607_, 1);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_val_613_);
v___x_615_ = v___x_605_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_val_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_a_618_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_602_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_602_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_vs_626_; lean_object* v___x_627_; lean_object* v___x_628_; size_t v_sz_629_; size_t v___x_630_; lean_object* v___x_631_; 
v_vs_626_ = lean_ctor_get(v_n_590_, 0);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_b_591_);
v_sz_629_ = lean_array_size(v_vs_626_);
v___x_630_ = ((size_t)0ULL);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__3(v_goal_589_, v_vs_626_, v_sz_629_, v___x_630_, v___x_628_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_646_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_646_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_646_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_646_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v_fst_636_; 
v_fst_636_ = lean_ctor_get(v_a_632_, 0);
if (lean_obj_tag(v_fst_636_) == 0)
{
lean_object* v_snd_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v_snd_637_ = lean_ctor_get(v_a_632_, 1);
lean_inc(v_snd_637_);
lean_dec(v_a_632_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_snd_637_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_638_);
v___x_640_ = v___x_634_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
else
{
lean_object* v_val_642_; lean_object* v___x_644_; 
lean_inc_ref(v_fst_636_);
lean_dec(v_a_632_);
v_val_642_ = lean_ctor_get(v_fst_636_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v_fst_636_, 1);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_val_642_);
v___x_644_ = v___x_634_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_val_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_647_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_631_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_631_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(lean_object* v_init_655_, lean_object* v_goal_656_, lean_object* v_as_657_, size_t v_sz_658_, size_t v_i_659_, lean_object* v_b_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = lean_usize_dec_lt(v_i_659_, v_sz_658_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v_b_660_);
return v___x_667_;
}
else
{
lean_object* v_snd_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_702_; 
v_snd_668_ = lean_ctor_get(v_b_660_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_b_660_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_b_660_, 0);
lean_dec(v_unused_703_);
v___x_670_ = v_b_660_;
v_isShared_671_ = v_isSharedCheck_702_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_snd_668_);
lean_dec(v_b_660_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_702_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_array_uget_borrowed(v_as_657_, v_i_659_);
lean_inc(v_snd_668_);
v___x_673_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_655_, v_goal_656_, v_a_672_, v_snd_668_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_693_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_693_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_693_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_693_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
if (lean_obj_tag(v_a_674_) == 0)
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v_a_674_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_678_);
v___x_680_ = v___x_670_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_snd_668_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_680_);
v___x_682_ = v___x_676_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
lean_del_object(v___x_676_);
lean_dec(v_snd_668_);
v_a_685_ = lean_ctor_get(v_a_674_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v_a_674_, 1);
v___x_686_ = lean_box(0);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_a_685_);
lean_ctor_set(v___x_670_, 0, v___x_686_);
v___x_688_ = v___x_670_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_a_685_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
size_t v___x_689_; size_t v___x_690_; 
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_i_659_, v___x_689_);
v_i_659_ = v___x_690_;
v_b_660_ = v___x_688_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_del_object(v___x_670_);
lean_dec(v_snd_668_);
v_a_694_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_673_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_673_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2___boxed(lean_object* v_init_704_, lean_object* v_goal_705_, lean_object* v_as_706_, lean_object* v_sz_707_, lean_object* v_i_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_707_);
lean_dec(v_sz_707_);
v_i_boxed_716_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1_spec__2(v_init_704_, v_goal_705_, v_as_706_, v_sz_boxed_715_, v_i_boxed_716_, v_b_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_as_706_);
lean_dec_ref(v_goal_705_);
lean_dec_ref(v_init_704_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1___boxed(lean_object* v_init_718_, lean_object* v_goal_719_, lean_object* v_n_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_718_, v_goal_719_, v_n_720_, v_b_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec_ref(v_n_720_);
lean_dec_ref(v_goal_719_);
lean_dec_ref(v_init_718_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(lean_object* v_goal_728_, lean_object* v_as_729_, size_t v_sz_730_, size_t v_i_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_lt(v_i_731_, v_sz_730_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v_b_732_);
return v___x_739_;
}
else
{
lean_object* v_snd_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_776_; 
v_snd_740_ = lean_ctor_get(v_b_732_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_b_732_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_b_732_, 0);
lean_dec(v_unused_777_);
v___x_742_ = v_b_732_;
v_isShared_743_ = v_isSharedCheck_776_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_snd_740_);
lean_dec(v_b_732_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_776_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_744_ = lean_array_uget_borrowed(v_as_729_, v_i_731_);
lean_inc(v_a_744_);
v___x_745_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_728_, v_a_744_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_self_747_; lean_object* v___x_748_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v_self_747_ = lean_ctor_get(v_a_746_, 0);
lean_inc_ref(v_self_747_);
lean_dec(v_a_746_);
v___x_748_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_728_, v_self_747_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = lean_box(0);
v___x_751_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v_snd_740_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_a_749_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_753_);
lean_ctor_set(v___x_742_, 0, v___x_750_);
v___x_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
size_t v___x_756_; size_t v___x_757_; 
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_731_, v___x_756_);
v_i_731_ = v___x_757_;
v_b_732_ = v___x_755_;
goto _start;
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_del_object(v___x_742_);
lean_dec(v_snd_740_);
v_a_760_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_748_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_748_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_del_object(v___x_742_);
lean_dec(v_snd_740_);
v_a_768_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_745_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_745_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5___boxed(lean_object* v_goal_778_, lean_object* v_as_779_, lean_object* v_sz_780_, lean_object* v_i_781_, lean_object* v_b_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
size_t v_sz_boxed_788_; size_t v_i_boxed_789_; lean_object* v_res_790_; 
v_sz_boxed_788_ = lean_unbox_usize(v_sz_780_);
lean_dec(v_sz_780_);
v_i_boxed_789_ = lean_unbox_usize(v_i_781_);
lean_dec(v_i_781_);
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(v_goal_778_, v_as_779_, v_sz_boxed_788_, v_i_boxed_789_, v_b_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec_ref(v_as_779_);
lean_dec_ref(v_goal_778_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(lean_object* v_goal_791_, lean_object* v_as_792_, size_t v_sz_793_, size_t v_i_794_, lean_object* v_b_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = lean_usize_dec_lt(v_i_794_, v_sz_793_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v_b_795_);
return v___x_802_;
}
else
{
lean_object* v_snd_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_839_; 
v_snd_803_ = lean_ctor_get(v_b_795_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_b_795_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v_b_795_, 0);
lean_dec(v_unused_840_);
v___x_805_ = v_b_795_;
v_isShared_806_ = v_isSharedCheck_839_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_snd_803_);
lean_dec(v_b_795_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_839_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_a_807_; lean_object* v___x_808_; 
v_a_807_ = lean_array_uget_borrowed(v_as_792_, v_i_794_);
lean_inc(v_a_807_);
v___x_808_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_791_, v_a_807_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_self_810_; lean_object* v___x_811_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v_self_810_ = lean_ctor_get(v_a_809_, 0);
lean_inc_ref(v_self_810_);
lean_dec(v_a_809_);
v___x_811_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_791_, v_self_810_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = lean_box(0);
v___x_814_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v_snd_803_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v_a_812_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_816_);
lean_ctor_set(v___x_805_, 0, v___x_813_);
v___x_818_ = v___x_805_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_794_, v___x_819_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2_spec__5(v_goal_791_, v_as_792_, v_sz_793_, v___x_820_, v___x_818_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_821_;
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_del_object(v___x_805_);
lean_dec(v_snd_803_);
v_a_823_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_811_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_811_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_del_object(v___x_805_);
lean_dec(v_snd_803_);
v_a_831_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_808_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_808_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2___boxed(lean_object* v_goal_841_, lean_object* v_as_842_, lean_object* v_sz_843_, lean_object* v_i_844_, lean_object* v_b_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
size_t v_sz_boxed_851_; size_t v_i_boxed_852_; lean_object* v_res_853_; 
v_sz_boxed_851_ = lean_unbox_usize(v_sz_843_);
lean_dec(v_sz_843_);
v_i_boxed_852_ = lean_unbox_usize(v_i_844_);
lean_dec(v_i_844_);
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(v_goal_841_, v_as_842_, v_sz_boxed_851_, v_i_boxed_852_, v_b_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_as_842_);
lean_dec_ref(v_goal_841_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(lean_object* v_goal_854_, lean_object* v_t_855_, lean_object* v_init_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_root_862_; lean_object* v_tail_863_; lean_object* v___x_864_; 
v_root_862_ = lean_ctor_get(v_t_855_, 0);
v_tail_863_ = lean_ctor_get(v_t_855_, 1);
lean_inc_ref(v_init_856_);
v___x_864_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_856_, v_goal_854_, v_root_862_, v_init_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec_ref(v_init_856_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_901_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_901_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_901_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_901_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
if (lean_obj_tag(v_a_865_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; 
v_a_869_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v_a_865_, 1);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v_a_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; size_t v_sz_876_; size_t v___x_877_; lean_object* v___x_878_; 
lean_del_object(v___x_867_);
v_a_873_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v_a_865_, 1);
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v_a_873_);
v_sz_876_ = lean_array_size(v_tail_863_);
v___x_877_ = ((size_t)0ULL);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__2(v_goal_854_, v_tail_863_, v_sz_876_, v___x_877_, v___x_875_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_892_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_892_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_892_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_892_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_fst_883_; 
v_fst_883_ = lean_ctor_get(v_a_879_, 0);
if (lean_obj_tag(v_fst_883_) == 0)
{
lean_object* v_snd_884_; lean_object* v___x_886_; 
v_snd_884_ = lean_ctor_get(v_a_879_, 1);
lean_inc(v_snd_884_);
lean_dec(v_a_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_snd_884_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_snd_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v_val_888_; lean_object* v___x_890_; 
lean_inc_ref(v_fst_883_);
lean_dec(v_a_879_);
v_val_888_ = lean_ctor_get(v_fst_883_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v_fst_883_, 1);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_val_888_);
v___x_890_ = v___x_881_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_val_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v_a_893_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_878_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_878_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v_a_902_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_864_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_864_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1___boxed(lean_object* v_goal_910_, lean_object* v_t_911_, lean_object* v_init_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(v_goal_910_, v_t_911_, v_init_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v_t_911_);
lean_dec_ref(v_goal_910_);
return v_res_918_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Goal_ppState___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v_r_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Meta_Grind_Goal_ppState___closed__0));
v_r_921_ = l_Lean_stringToMessageData(v___x_920_);
return v_r_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object* v_goal_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_toGoalState_928_; lean_object* v_exprs_929_; lean_object* v_r_930_; lean_object* v___x_931_; 
v_toGoalState_928_ = lean_ctor_get(v_goal_922_, 0);
v_exprs_929_ = lean_ctor_get(v_toGoalState_928_, 2);
v_r_930_ = lean_obj_once(&l_Lean_Meta_Grind_Goal_ppState___closed__1, &l_Lean_Meta_Grind_Goal_ppState___closed__1_once, _init_l_Lean_Meta_Grind_Goal_ppState___closed__1);
v___x_931_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1(v_goal_922_, v_exprs_929_, v_r_930_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = 1;
v___x_934_ = l_Lean_Meta_Grind_Goal_getEqcs(v_goal_922_, v___x_933_);
v___x_935_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_922_, v___x_934_, v_a_932_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v___x_934_);
return v___x_935_;
}
else
{
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_ppState___boxed(lean_object* v_goal_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Meta_Grind_Goal_ppState(v_goal_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec_ref(v_goal_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(lean_object* v_goal_943_, lean_object* v_as_944_, lean_object* v_as_x27_945_, lean_object* v_b_946_, lean_object* v_a_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg(v_goal_943_, v_as_x27_945_, v_b_946_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___boxed(lean_object* v_goal_954_, lean_object* v_as_955_, lean_object* v_as_x27_956_, lean_object* v_b_957_, lean_object* v_a_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2(v_goal_954_, v_as_955_, v_as_x27_956_, v_b_957_, v_a_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v_as_x27_956_);
lean_dec(v_as_955_);
lean_dec_ref(v_goal_954_);
return v_res_964_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_box(1);
v___x_966_ = l_Lean_MessageData_ofFormat(v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(lean_object* v_as_x27_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
if (lean_obj_tag(v_as_x27_967_) == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_b_968_);
return v___x_974_;
}
else
{
lean_object* v_head_975_; lean_object* v_tail_976_; lean_object* v___x_977_; 
v_head_975_ = lean_ctor_get(v_as_x27_967_, 0);
v_tail_976_ = lean_ctor_get(v_as_x27_967_, 1);
v___x_977_ = l_Lean_Meta_Grind_Goal_ppState(v_head_975_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v_b_968_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v_a_978_);
v_as_x27_967_ = v_tail_976_;
v_b_968_ = v___x_981_;
goto _start;
}
else
{
lean_dec_ref(v_b_968_);
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___boxed(lean_object* v_as_x27_983_, lean_object* v_b_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_as_x27_983_, v_b_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v_as_x27_983_);
return v_res_990_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppGoals___closed__1(void){
_start:
{
lean_object* v___x_992_; lean_object* v_r_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v_r_993_ = l_Lean_stringToMessageData(v___x_992_);
return v_r_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppGoals(lean_object* v_goals_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_r_1000_; lean_object* v___x_1001_; 
v_r_1000_ = lean_obj_once(&l_Lean_Meta_Grind_ppGoals___closed__1, &l_Lean_Meta_Grind_ppGoals___closed__1_once, _init_l_Lean_Meta_Grind_ppGoals___closed__1);
v___x_1001_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_goals_994_, v_r_1000_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppGoals___boxed(lean_object* v_goals_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_Meta_Grind_ppGoals(v_goals_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_goals_1002_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(lean_object* v_as_1009_, lean_object* v_as_x27_1010_, lean_object* v_b_1011_, lean_object* v_a_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg(v_as_x27_1010_, v_b_1011_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___boxed(lean_object* v_as_1019_, lean_object* v_as_x27_1020_, lean_object* v_b_1021_, lean_object* v_a_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0(v_as_1019_, v_as_x27_1020_, v_b_1021_, v_a_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v_as_x27_1020_);
lean_dec(v_as_1019_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(lean_object* v_m_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_array_push(v_a_1030_, v_m_1029_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg___boxed(lean_object* v_m_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_m_1036_, v_a_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(lean_object* v_m_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_m_1040_, v_a_1042_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___boxed(lean_object* v_m_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg(v_m_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec_ref(v_a_1050_);
return v_res_1057_;
}
}
static double _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1058_; double v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_float_of_nat(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(lean_object* v_e_1062_, lean_object* v_cls_1063_){
_start:
{
lean_object* v___x_1064_; double v___x_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1066_ = 1;
v___x_1067_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1068_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1068_, 0, v_cls_1063_);
lean_ctor_set(v___x_1068_, 1, v___x_1064_);
lean_ctor_set(v___x_1068_, 2, v___x_1067_);
lean_ctor_set_float(v___x_1068_, sizeof(void*)*3, v___x_1065_);
lean_ctor_set_float(v___x_1068_, sizeof(void*)*3 + 8, v___x_1065_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*3 + 16, v___x_1066_);
v___x_1069_ = l_Lean_MessageData_ofExpr(v_e_1062_);
v___x_1070_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1071_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1068_);
lean_ctor_set(v___x_1071_, 1, v___x_1069_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(lean_object* v_clsElem_1072_, size_t v_sz_1073_, size_t v_i_1074_, lean_object* v_bs_1075_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_usize_dec_lt(v_i_1074_, v_sz_1073_);
if (v___x_1076_ == 0)
{
lean_dec(v_clsElem_1072_);
return v_bs_1075_;
}
else
{
lean_object* v_v_1077_; lean_object* v___x_1078_; lean_object* v_bs_x27_1079_; lean_object* v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v_v_1077_ = lean_array_uget(v_bs_1075_, v_i_1074_);
v___x_1078_ = lean_unsigned_to_nat(0u);
v_bs_x27_1079_ = lean_array_uset(v_bs_1075_, v_i_1074_, v___x_1078_);
lean_inc(v_clsElem_1072_);
v___x_1080_ = l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0(v_v_1077_, v_clsElem_1072_);
v___x_1081_ = ((size_t)1ULL);
v___x_1082_ = lean_usize_add(v_i_1074_, v___x_1081_);
v___x_1083_ = lean_array_uset(v_bs_x27_1079_, v_i_1074_, v___x_1080_);
v_i_1074_ = v___x_1082_;
v_bs_1075_ = v___x_1083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1___boxed(lean_object* v_clsElem_1085_, lean_object* v_sz_1086_, lean_object* v_i_1087_, lean_object* v_bs_1088_){
_start:
{
size_t v_sz_boxed_1089_; size_t v_i_boxed_1090_; lean_object* v_res_1091_; 
v_sz_boxed_1089_ = lean_unbox_usize(v_sz_1086_);
lean_dec(v_sz_1086_);
v_i_boxed_1090_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(v_clsElem_1085_, v_sz_boxed_1089_, v_i_boxed_1090_, v_bs_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppExprArray(lean_object* v_cls_1092_, lean_object* v_header_1093_, lean_object* v_es_1094_, lean_object* v_clsElem_1095_, uint8_t v_collapsed_1096_){
_start:
{
size_t v_sz_1097_; size_t v___x_1098_; lean_object* v_es_1099_; lean_object* v___x_1100_; double v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_sz_1097_ = lean_array_size(v_es_1094_);
v___x_1098_ = ((size_t)0ULL);
v_es_1099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_ppExprArray_spec__1(v_clsElem_1095_, v_sz_1097_, v___x_1098_, v_es_1094_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1103_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1103_, 0, v_cls_1092_);
lean_ctor_set(v___x_1103_, 1, v___x_1100_);
lean_ctor_set(v___x_1103_, 2, v___x_1102_);
lean_ctor_set_float(v___x_1103_, sizeof(void*)*3, v___x_1101_);
lean_ctor_set_float(v___x_1103_, sizeof(void*)*3 + 8, v___x_1101_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*3 + 16, v_collapsed_1096_);
v___x_1104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_header_1093_);
v___x_1105_ = l_Lean_MessageData_ofFormat(v___x_1104_);
v___x_1106_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
lean_ctor_set(v___x_1106_, 2, v_es_1099_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppExprArray___boxed(lean_object* v_cls_1107_, lean_object* v_header_1108_, lean_object* v_es_1109_, lean_object* v_clsElem_1110_, lean_object* v_collapsed_1111_){
_start:
{
uint8_t v_collapsed_boxed_1112_; lean_object* v_res_1113_; 
v_collapsed_boxed_1112_ = lean_unbox(v_collapsed_1111_);
v_res_1113_ = l_Lean_Meta_Grind_ppExprArray(v_cls_1107_, v_header_1108_, v_es_1109_, v_clsElem_1110_, v_collapsed_boxed_1112_);
return v_res_1113_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(lean_object* v_declName_1124_){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__1));
v___x_1126_ = lean_name_eq(v_declName_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___closed__3));
v___x_1128_ = lean_name_eq(v_declName_1124_, v___x_1127_);
return v___x_1128_;
}
else
{
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget___boxed(lean_object* v_declName_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(v_declName_1129_);
lean_dec(v_declName_1129_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(lean_object* v_declName_1141_){
_start:
{
uint8_t v___y_1143_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3));
v___x_1147_ = lean_name_eq(v_declName_1141_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5));
v___x_1149_ = lean_name_eq(v_declName_1141_, v___x_1148_);
v___y_1143_ = v___x_1149_;
goto v___jp_1142_;
}
else
{
v___y_1143_ = v___x_1147_;
goto v___jp_1142_;
}
v___jp_1142_:
{
if (v___y_1143_ == 0)
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1));
v___x_1145_ = lean_name_eq(v_declName_1141_, v___x_1144_);
return v___x_1145_;
}
else
{
return v___y_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___boxed(lean_object* v_declName_1150_){
_start:
{
uint8_t v_res_1151_; lean_object* v_r_1152_; 
v_res_1151_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_1150_);
lean_dec(v_declName_1150_);
v_r_1152_ = lean_box(v_res_1151_);
return v_r_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(uint8_t v_x_1153_){
_start:
{
switch(v_x_1153_)
{
case 0:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_unsigned_to_nat(0u);
return v___x_1154_;
}
case 1:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_unsigned_to_nat(1u);
return v___x_1155_;
}
default: 
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_unsigned_to_nat(2u);
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___boxed(lean_object* v_x_1157_){
_start:
{
uint8_t v_x_boxed_1158_; lean_object* v_res_1159_; 
v_x_boxed_1158_ = lean_unbox(v_x_1157_);
v_res_1159_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(v_x_boxed_1158_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(uint8_t v_x_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx(v_x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx___boxed(lean_object* v_x_1162_){
_start:
{
uint8_t v_x_4__boxed_1163_; lean_object* v_res_1164_; 
v_x_4__boxed_1163_ = lean_unbox(v_x_1162_);
v_res_1164_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_toCtorIdx(v_x_4__boxed_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(lean_object* v_k_1165_){
_start:
{
lean_inc(v_k_1165_);
return v_k_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg___boxed(lean_object* v_k_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(v_k_1166_);
lean_dec(v_k_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(lean_object* v_motive_1168_, lean_object* v_ctorIdx_1169_, uint8_t v_t_1170_, lean_object* v_h_1171_, lean_object* v_k_1172_){
_start:
{
lean_inc(v_k_1172_);
return v_k_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___boxed(lean_object* v_motive_1173_, lean_object* v_ctorIdx_1174_, lean_object* v_t_1175_, lean_object* v_h_1176_, lean_object* v_k_1177_){
_start:
{
uint8_t v_t_boxed_1178_; lean_object* v_res_1179_; 
v_t_boxed_1178_ = lean_unbox(v_t_1175_);
v_res_1179_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(v_motive_1173_, v_ctorIdx_1174_, v_t_boxed_1178_, v_h_1176_, v_k_1177_);
lean_dec(v_k_1177_);
lean_dec(v_ctorIdx_1174_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(lean_object* v_num_1180_){
_start:
{
lean_inc(v_num_1180_);
return v_num_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg___boxed(lean_object* v_num_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(v_num_1181_);
lean_dec(v_num_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(lean_object* v_motive_1183_, uint8_t v_t_1184_, lean_object* v_h_1185_, lean_object* v_num_1186_){
_start:
{
lean_inc(v_num_1186_);
return v_num_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___boxed(lean_object* v_motive_1187_, lean_object* v_t_1188_, lean_object* v_h_1189_, lean_object* v_num_1190_){
_start:
{
uint8_t v_t_boxed_1191_; lean_object* v_res_1192_; 
v_t_boxed_1191_ = lean_unbox(v_t_1188_);
v_res_1192_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(v_motive_1187_, v_t_boxed_1191_, v_h_1189_, v_num_1190_);
lean_dec(v_num_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(lean_object* v_cast_1193_){
_start:
{
lean_inc(v_cast_1193_);
return v_cast_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg___boxed(lean_object* v_cast_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(v_cast_1194_);
lean_dec(v_cast_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(lean_object* v_motive_1196_, uint8_t v_t_1197_, lean_object* v_h_1198_, lean_object* v_cast_1199_){
_start:
{
lean_inc(v_cast_1199_);
return v_cast_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___boxed(lean_object* v_motive_1200_, lean_object* v_t_1201_, lean_object* v_h_1202_, lean_object* v_cast_1203_){
_start:
{
uint8_t v_t_boxed_1204_; lean_object* v_res_1205_; 
v_t_boxed_1204_ = lean_unbox(v_t_1201_);
v_res_1205_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(v_motive_1200_, v_t_boxed_1204_, v_h_1202_, v_cast_1203_);
lean_dec(v_cast_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(lean_object* v_no_1206_){
_start:
{
lean_inc(v_no_1206_);
return v_no_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg___boxed(lean_object* v_no_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(v_no_1207_);
lean_dec(v_no_1207_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(lean_object* v_motive_1209_, uint8_t v_t_1210_, lean_object* v_h_1211_, lean_object* v_no_1212_){
_start:
{
lean_inc(v_no_1212_);
return v_no_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___boxed(lean_object* v_motive_1213_, lean_object* v_t_1214_, lean_object* v_h_1215_, lean_object* v_no_1216_){
_start:
{
uint8_t v_t_boxed_1217_; lean_object* v_res_1218_; 
v_t_boxed_1217_ = lean_unbox(v_t_1214_);
v_res_1218_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(v_motive_1213_, v_t_boxed_1217_, v_h_1215_, v_no_1216_);
lean_dec(v_no_1216_);
return v_res_1218_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedResult_default(void){
_start:
{
uint8_t v___x_1219_; 
v___x_1219_ = 0;
return v___x_1219_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult(void){
_start:
{
uint8_t v___x_1220_; 
v___x_1220_ = 0;
return v___x_1220_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(lean_object* v_e_1261_){
_start:
{
lean_object* v_a_1267_; lean_object* v_b_1268_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
lean_inc_ref(v_e_1261_);
v___x_1272_ = l_Lean_Expr_cleanupAnnotations(v_e_1261_);
v___x_1273_ = l_Lean_Expr_isApp(v___x_1272_);
if (v___x_1273_ == 0)
{
lean_dec_ref(v___x_1272_);
goto v___jp_1262_;
}
else
{
lean_object* v_arg_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_arg_1274_ = lean_ctor_get(v___x_1272_, 1);
lean_inc_ref(v_arg_1274_);
v___x_1275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1272_);
v___x_1276_ = l_Lean_Expr_isApp(v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_arg_1274_);
goto v___jp_1262_;
}
else
{
lean_object* v_arg_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_arg_1277_ = lean_ctor_get(v___x_1275_, 1);
lean_inc_ref(v_arg_1277_);
v___x_1278_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1275_);
v___x_1279_ = l_Lean_Expr_isApp(v___x_1278_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v___x_1278_);
lean_dec_ref(v_arg_1277_);
lean_dec_ref(v_arg_1274_);
goto v___jp_1262_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1278_);
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2));
v___x_1282_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5));
v___x_1284_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1283_);
if (v___x_1284_ == 0)
{
uint8_t v___x_1285_; 
v___x_1285_ = l_Lean_Expr_isApp(v___x_1280_);
if (v___x_1285_ == 0)
{
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1277_);
lean_dec_ref(v_arg_1274_);
goto v___jp_1262_;
}
else
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1280_);
v___x_1287_ = l_Lean_Expr_isApp(v___x_1286_);
if (v___x_1287_ == 0)
{
lean_dec_ref(v___x_1286_);
lean_dec_ref(v_arg_1277_);
lean_dec_ref(v_arg_1274_);
goto v___jp_1262_;
}
else
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1286_);
v___x_1289_ = l_Lean_Expr_isApp(v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec_ref(v___x_1288_);
lean_dec_ref(v_arg_1277_);
lean_dec_ref(v_arg_1274_);
goto v___jp_1262_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1290_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1288_);
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8));
v___x_1292_ = l_Lean_Expr_isConstOf(v___x_1290_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11));
v___x_1294_ = l_Lean_Expr_isConstOf(v___x_1290_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14));
v___x_1296_ = l_Lean_Expr_isConstOf(v___x_1290_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17));
v___x_1298_ = l_Lean_Expr_isConstOf(v___x_1290_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20));
v___x_1300_ = l_Lean_Expr_isConstOf(v___x_1290_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23));
v___x_1302_ = l_Lean_Expr_isConstOf(v___x_1290_, v___x_1301_);
lean_dec_ref(v___x_1290_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v_arg_1277_);
lean_dec_ref(v_arg_1274_);
goto v___jp_1262_;
}
else
{
lean_dec_ref(v_e_1261_);
v_a_1267_ = v_arg_1277_;
v_b_1268_ = v_arg_1274_;
goto v___jp_1266_;
}
}
else
{
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_e_1261_);
v_a_1267_ = v_arg_1277_;
v_b_1268_ = v_arg_1274_;
goto v___jp_1266_;
}
}
else
{
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_e_1261_);
v_a_1267_ = v_arg_1277_;
v_b_1268_ = v_arg_1274_;
goto v___jp_1266_;
}
}
else
{
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_e_1261_);
v_a_1267_ = v_arg_1277_;
v_b_1268_ = v_arg_1274_;
goto v___jp_1266_;
}
}
else
{
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_e_1261_);
v_a_1267_ = v_arg_1277_;
v_b_1268_ = v_arg_1274_;
goto v___jp_1266_;
}
}
else
{
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_arg_1274_);
lean_dec_ref(v_e_1261_);
v_e_1261_ = v_arg_1277_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1277_);
lean_dec_ref(v_e_1261_);
v_e_1261_ = v_arg_1274_;
goto _start;
}
}
else
{
uint8_t v___x_1305_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1277_);
lean_dec_ref(v_arg_1274_);
lean_dec_ref(v_e_1261_);
v___x_1305_ = 0;
return v___x_1305_;
}
}
}
}
v___jp_1262_:
{
uint8_t v___x_1263_; 
v___x_1263_ = l_Lean_Meta_Grind_isCastLikeApp(v_e_1261_);
lean_dec_ref(v_e_1261_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = 2;
return v___x_1264_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = 1;
return v___x_1265_;
}
}
v___jp_1266_:
{
uint8_t v___x_1269_; 
v___x_1269_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_a_1267_);
switch(v___x_1269_)
{
case 0:
{
uint8_t v___x_1270_; 
v___x_1270_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_1268_);
if (v___x_1270_ == 0)
{
return v___x_1270_;
}
else
{
return v___x_1270_;
}
}
case 1:
{
uint8_t v___x_1271_; 
v___x_1271_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_1268_);
switch(v___x_1271_)
{
case 2:
{
return v___x_1271_;
}
case 1:
{
return v___x_1271_;
}
default: 
{
return v___x_1269_;
}
}
}
default: 
{
lean_dec_ref(v_b_1268_);
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___boxed(lean_object* v_e_1306_){
_start:
{
uint8_t v_res_1307_; lean_object* v_r_1308_; 
v_res_1307_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_1306_);
v_r_1308_ = lean_box(v_res_1307_);
return v_r_1308_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(lean_object* v_e_1309_){
_start:
{
uint8_t v___x_1310_; 
v___x_1310_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_1309_);
if (v___x_1310_ == 1)
{
uint8_t v___x_1311_; 
v___x_1311_ = 1;
return v___x_1311_;
}
else
{
uint8_t v___x_1312_; 
v___x_1312_ = 0;
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike___boxed(lean_object* v_e_1313_){
_start:
{
uint8_t v_res_1314_; lean_object* v_r_1315_; 
v_res_1314_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_1313_);
v_r_1315_ = lean_box(v_res_1314_);
return v_r_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(lean_object* v_declName_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v_env_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = lean_st_ref_get(v___y_1317_);
v_env_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc_ref(v_env_1320_);
lean_dec(v___x_1319_);
v___x_1321_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1320_, v_declName_1316_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg___boxed(lean_object* v_declName_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1323_, v___y_1324_);
lean_dec(v___y_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(lean_object* v_declName_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1327_, v___y_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___boxed(lean_object* v_declName_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(v_declName_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp(lean_object* v_e_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
uint8_t v___x_1347_; uint8_t v___x_1348_; 
lean_inc_ref(v_e_1341_);
v___x_1347_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_1341_);
v___x_1348_ = 1;
if (v___x_1347_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Expr_getAppFn(v_e_1341_);
if (lean_obj_tag(v___x_1349_) == 4)
{
lean_object* v_declName_1350_; lean_object* v___y_1352_; lean_object* v___x_1367_; lean_object* v_a_1368_; 
v_declName_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_n(v_declName_1350_, 2);
lean_dec_ref_known(v___x_1349_, 2);
v___x_1367_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1350_, v_a_1345_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref(v___x_1367_);
if (lean_obj_tag(v_a_1368_) == 1)
{
lean_object* v_val_1369_; lean_object* v_numParams_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_val_1369_ = lean_ctor_get(v_a_1368_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v_a_1368_, 1);
v_numParams_1370_ = lean_ctor_get(v_val_1369_, 1);
lean_inc(v_numParams_1370_);
lean_dec(v_val_1369_);
v___x_1371_ = l_Lean_Expr_getAppNumArgs(v_e_1341_);
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_nat_add(v_numParams_1370_, v___x_1372_);
lean_dec(v_numParams_1370_);
v___x_1374_ = lean_nat_dec_eq(v___x_1371_, v___x_1373_);
lean_dec(v___x_1373_);
lean_dec(v___x_1371_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v_e_1341_);
v___y_1352_ = v_a_1345_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = l_Lean_Expr_appArg_x21(v_e_1341_);
lean_dec_ref(v_e_1341_);
v___x_1376_ = l_Lean_Meta_isConstructorApp(v___x_1375_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1386_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1386_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1386_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_unbox(v_a_1377_);
lean_dec(v_a_1377_);
if (v___x_1381_ == 0)
{
lean_del_object(v___x_1379_);
v___y_1352_ = v_a_1345_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_dec(v_declName_1350_);
v___x_1382_ = lean_box(v___x_1348_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_dec(v_declName_1350_);
return v___x_1376_;
}
}
}
else
{
lean_dec(v_a_1368_);
lean_dec_ref(v_e_1341_);
v___y_1352_ = v_a_1345_;
goto v___jp_1351_;
}
v___jp_1351_:
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = lean_st_ref_get(v___y_1352_);
v___x_1354_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_1350_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; 
v___x_1355_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(v_declName_1350_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
v___x_1356_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_1350_);
if (v___x_1356_ == 0)
{
lean_object* v_env_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_env_1357_ = lean_ctor_get(v___x_1353_, 0);
lean_inc_ref(v_env_1357_);
lean_dec(v___x_1353_);
v___x_1358_ = l_Lean_Meta_isMatcherCore(v_env_1357_, v_declName_1350_);
v___x_1359_ = lean_box(v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v___x_1353_);
lean_dec(v_declName_1350_);
v___x_1361_ = lean_box(v___x_1348_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_dec(v___x_1353_);
lean_dec(v_declName_1350_);
v___x_1363_ = lean_box(v___x_1348_);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v___x_1353_);
lean_dec(v_declName_1350_);
v___x_1365_ = lean_box(v___x_1348_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec_ref(v___x_1349_);
lean_dec_ref(v_e_1341_);
v___x_1387_ = lean_box(v___x_1347_);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v_e_1341_);
v___x_1389_ = lean_box(v___x_1348_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp___boxed(lean_object* v_e_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Meta_Grind_isSupportApp(v_e_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
if (lean_obj_tag(v_a_1398_) == 0)
{
lean_object* v___x_1400_; 
v___x_1400_ = l_List_reverse___redArg(v_a_1399_);
return v___x_1400_;
}
else
{
lean_object* v_head_1401_; lean_object* v_tail_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1411_; 
v_head_1401_ = lean_ctor_get(v_a_1398_, 0);
v_tail_1402_ = lean_ctor_get(v_a_1398_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_a_1398_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1404_ = v_a_1398_;
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_tail_1402_);
lean_inc(v_head_1401_);
lean_dec(v_a_1398_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1411_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = l_Lean_MessageData_ofExpr(v_head_1401_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v_a_1399_);
lean_ctor_set(v___x_1404_, 0, v___x_1406_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_a_1399_);
v___x_1408_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
v_a_1398_ = v_tail_1402_;
v_a_1399_ = v___x_1408_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__2(void){
_start:
{
lean_object* v___x_1415_; uint8_t v___x_1416_; double v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1415_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1416_ = 1;
v___x_1417_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1418_ = lean_box(0);
v___x_1419_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1420_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v___x_1418_);
lean_ctor_set(v___x_1420_, 2, v___x_1415_);
lean_ctor_set_float(v___x_1420_, sizeof(void*)*3, v___x_1417_);
lean_ctor_set_float(v___x_1420_, sizeof(void*)*3 + 8, v___x_1417_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*3 + 16, v___x_1416_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__5(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__4));
v___x_1425_ = l_Lean_MessageData_ofFormat(v___x_1424_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__6(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
v___x_1427_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__5, &l_Lean_Meta_Grind_ppEqc___closed__5_once, _init_l_Lean_Meta_Grind_ppEqc___closed__5);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v___x_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppEqc(lean_object* v_eqc_1429_, lean_object* v_children_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1431_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__2, &l_Lean_Meta_Grind_ppEqc___closed__2_once, _init_l_Lean_Meta_Grind_ppEqc___closed__2);
v___x_1432_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
v___x_1433_ = lean_box(0);
v___x_1434_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(v_eqc_1429_, v___x_1433_);
v___x_1435_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__6, &l_Lean_Meta_Grind_ppEqc___closed__6_once, _init_l_Lean_Meta_Grind_ppEqc___closed__6);
v___x_1436_ = l_Lean_MessageData_joinSep(v___x_1434_, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1432_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1431_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_ctor_set(v___x_1441_, 2, v_children_1430_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
if (lean_obj_tag(v_a_1442_) == 0)
{
lean_object* v___x_1444_; 
v___x_1444_ = l_List_reverse___redArg(v_a_1443_);
return v___x_1444_;
}
else
{
lean_object* v_head_1445_; lean_object* v_tail_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1457_; 
v_head_1445_ = lean_ctor_get(v_a_1442_, 0);
v_tail_1446_ = lean_ctor_get(v_a_1442_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_a_1442_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1448_ = v_a_1442_;
v_isShared_1449_ = v_isSharedCheck_1457_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_tail_1446_);
lean_inc(v_head_1445_);
lean_dec(v_a_1442_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1457_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
uint8_t v___x_1450_; uint8_t v___x_1451_; 
lean_inc(v_head_1445_);
v___x_1450_ = l_Lean_Expr_isTrue(v_head_1445_);
v___x_1451_ = lean_bool_not(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_del_object(v___x_1448_);
lean_dec(v_head_1445_);
v_a_1442_ = v_tail_1446_;
goto _start;
}
else
{
lean_object* v___x_1454_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v_a_1443_);
v___x_1454_ = v___x_1448_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_head_1445_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_a_1443_);
v___x_1454_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
v_a_1442_ = v_tail_1446_;
v_a_1443_ = v___x_1454_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
if (lean_obj_tag(v_a_1458_) == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = l_List_reverse___redArg(v_a_1459_);
return v___x_1460_;
}
else
{
lean_object* v_head_1461_; lean_object* v_tail_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1473_; 
v_head_1461_ = lean_ctor_get(v_a_1458_, 0);
v_tail_1462_ = lean_ctor_get(v_a_1458_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_a_1458_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1464_ = v_a_1458_;
v_isShared_1465_ = v_isSharedCheck_1473_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_tail_1462_);
lean_inc(v_head_1461_);
lean_dec(v_a_1458_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1473_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
uint8_t v___x_1466_; uint8_t v___x_1467_; 
lean_inc(v_head_1461_);
v___x_1466_ = l_Lean_Expr_isFalse(v_head_1461_);
v___x_1467_ = lean_bool_not(v___x_1466_);
if (v___x_1467_ == 0)
{
lean_del_object(v___x_1464_);
lean_dec(v_head_1461_);
v_a_1458_ = v_tail_1462_;
goto _start;
}
else
{
lean_object* v___x_1470_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v_a_1459_);
v___x_1470_ = v___x_1464_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_head_1461_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_a_1459_);
v___x_1470_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
v_a_1458_ = v_tail_1462_;
v_a_1459_ = v___x_1470_;
goto _start;
}
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_x_1530_);
lean_ctor_set(v___x_1537_, 1, v___y_1531_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v_head_1539_; lean_object* v_tail_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1561_; 
v_head_1539_ = lean_ctor_get(v_x_1529_, 0);
v_tail_1540_ = lean_ctor_get(v_x_1529_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1542_ = v_x_1529_;
v_isShared_1543_ = v_isSharedCheck_1561_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_tail_1540_);
lean_inc(v_head_1539_);
lean_dec(v_x_1529_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1561_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; 
lean_inc(v_head_1539_);
v___x_1544_ = l_Lean_Meta_Grind_isSupportApp(v_head_1539_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; uint8_t v___x_1546_; uint8_t v___x_1547_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = lean_unbox(v_a_1545_);
lean_dec(v_a_1545_);
v___x_1547_ = lean_bool_not(v___x_1546_);
if (v___x_1547_ == 0)
{
lean_del_object(v___x_1542_);
lean_dec(v_head_1539_);
v_x_1529_ = v_tail_1540_;
goto _start;
}
else
{
lean_object* v___x_1550_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v_x_1530_);
v___x_1550_ = v___x_1542_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_head_1539_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_x_1530_);
v___x_1550_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
v_x_1529_ = v_tail_1540_;
v_x_1530_ = v___x_1550_;
goto _start;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_del_object(v___x_1542_);
lean_dec(v_tail_1540_);
lean_dec(v_head_1539_);
lean_dec_ref(v___y_1531_);
lean_dec(v_x_1530_);
v_a_1553_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1544_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1544_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg___boxed(lean_object* v_x_1562_, lean_object* v_x_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_x_1562_, v_x_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(uint8_t v_collapsedProps_1576_, lean_object* v_as_x27_1577_, lean_object* v_b_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
if (lean_obj_tag(v_as_x27_1577_) == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_b_1578_);
lean_ctor_set(v___x_1586_, 1, v___y_1580_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
return v___x_1587_;
}
else
{
lean_object* v_snd_1588_; lean_object* v_snd_1589_; lean_object* v_head_1590_; lean_object* v_tail_1591_; lean_object* v_fst_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1755_; 
v_snd_1588_ = lean_ctor_get(v_b_1578_, 1);
lean_inc(v_snd_1588_);
v_snd_1589_ = lean_ctor_get(v_snd_1588_, 1);
lean_inc(v_snd_1589_);
v_head_1590_ = lean_ctor_get(v_as_x27_1577_, 0);
v_tail_1591_ = lean_ctor_get(v_as_x27_1577_, 1);
v_fst_1592_ = lean_ctor_get(v_b_1578_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_b_1578_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_b_1578_, 1);
lean_dec(v_unused_1756_);
v___x_1594_ = v_b_1578_;
v_isShared_1595_ = v_isSharedCheck_1755_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_fst_1592_);
lean_dec(v_b_1578_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1755_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_fst_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1753_; 
v_fst_1596_ = lean_ctor_get(v_snd_1588_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_snd_1588_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v_snd_1588_, 1);
lean_dec(v_unused_1754_);
v___x_1598_ = v_snd_1588_;
v_isShared_1599_ = v_isSharedCheck_1753_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_fst_1596_);
lean_dec(v_snd_1588_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1753_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_fst_1600_; lean_object* v_snd_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1752_; 
v_fst_1600_ = lean_ctor_get(v_snd_1589_, 0);
v_snd_1601_ = lean_ctor_get(v_snd_1589_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_snd_1589_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1603_ = v_snd_1589_;
v_isShared_1604_ = v_isSharedCheck_1752_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_snd_1601_);
lean_inc(v_fst_1600_);
lean_dec(v_snd_1589_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1752_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___y_1606_; lean_object* v___x_1617_; 
lean_inc(v_head_1590_);
v___x_1617_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(v_head_1590_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v___x_1618_; 
lean_inc(v_head_1590_);
v___x_1618_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(v_head_1590_);
if (lean_obj_tag(v___x_1618_) == 0)
{
if (lean_obj_tag(v_head_1590_) == 1)
{
lean_object* v_tail_1619_; 
v_tail_1619_ = lean_ctor_get(v_head_1590_, 1);
if (lean_obj_tag(v_tail_1619_) == 1)
{
lean_object* v_head_1620_; lean_object* v___x_1621_; 
lean_del_object(v___x_1603_);
lean_del_object(v___x_1598_);
lean_del_object(v___x_1594_);
v_head_1620_ = lean_ctor_get(v_head_1590_, 0);
lean_inc(v_head_1620_);
v___x_1621_ = l_Lean_Meta_isProof(v_head_1620_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; uint8_t v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = lean_unbox(v_a_1622_);
lean_dec(v_a_1622_);
if (v___x_1623_ == 0)
{
lean_object* v_regularEqcs_1624_; lean_object* v___y_1626_; lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v_fst_1647_; lean_object* v_snd_1648_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_regularEqcs_1624_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1675_ = lean_box(0);
lean_inc_ref(v_head_1590_);
v___x_1676_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_head_1590_, v___x_1675_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; lean_object* v___x_1680_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v_fst_1678_ = lean_ctor_get(v_a_1677_, 0);
lean_inc(v_fst_1678_);
v_snd_1679_ = lean_ctor_get(v_a_1677_, 1);
lean_inc(v_snd_1679_);
lean_dec(v_a_1677_);
v___x_1680_ = l_List_reverse___redArg(v_fst_1678_);
v_fst_1647_ = v___x_1680_;
v_snd_1648_ = v_snd_1679_;
goto v___jp_1646_;
}
else
{
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1681_; lean_object* v_fst_1682_; lean_object* v_snd_1683_; 
v_a_1681_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1676_, 1);
v_fst_1682_ = lean_ctor_get(v_a_1681_, 0);
lean_inc(v_fst_1682_);
v_snd_1683_ = lean_ctor_get(v_a_1681_, 1);
lean_inc(v_snd_1683_);
lean_dec(v_a_1681_);
v_fst_1647_ = v_fst_1682_;
v_snd_1648_ = v_snd_1683_;
goto v___jp_1646_;
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_snd_1601_);
lean_dec(v_fst_1600_);
lean_dec(v_fst_1596_);
lean_dec(v_fst_1592_);
v_a_1684_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1676_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1676_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
v___jp_1625_:
{
uint8_t v___x_1629_; 
v___x_1629_ = l_List_isEmpty___redArg(v_fst_1627_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1630_ = l_Lean_Meta_Grind_ppEqc(v_fst_1627_, v_regularEqcs_1624_);
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___x_1633_ = lean_array_push(v___x_1632_, v___x_1630_);
v___x_1634_ = l_Lean_Meta_Grind_ppEqc(v___y_1626_, v___x_1633_);
v___x_1635_ = lean_array_push(v_fst_1600_, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v_snd_1601_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_fst_1596_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_fst_1592_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1638_;
v___y_1580_ = v_snd_1628_;
goto _start;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v_fst_1627_);
v___x_1640_ = l_Lean_Meta_Grind_ppEqc(v___y_1626_, v_regularEqcs_1624_);
v___x_1641_ = lean_array_push(v_fst_1600_, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_snd_1601_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_fst_1596_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_fst_1592_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1644_;
v___y_1580_ = v_snd_1628_;
goto _start;
}
}
v___jp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1649_ = l_List_lengthTR___redArg(v_fst_1647_);
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_nat_dec_le(v___x_1649_, v___x_1650_);
lean_dec(v___x_1649_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_box(0);
lean_inc_ref(v_head_1590_);
v___x_1653_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_head_1590_, v___x_1652_, v_snd_1648_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v_fst_1655_; lean_object* v_snd_1656_; lean_object* v___x_1657_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v_fst_1655_ = lean_ctor_get(v_a_1654_, 0);
lean_inc(v_fst_1655_);
v_snd_1656_ = lean_ctor_get(v_a_1654_, 1);
lean_inc(v_snd_1656_);
lean_dec(v_a_1654_);
v___x_1657_ = l_List_reverse___redArg(v_fst_1655_);
v___y_1626_ = v_fst_1647_;
v_fst_1627_ = v___x_1657_;
v_snd_1628_ = v_snd_1656_;
goto v___jp_1625_;
}
else
{
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1658_; lean_object* v_fst_1659_; lean_object* v_snd_1660_; 
v_a_1658_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1653_, 1);
v_fst_1659_ = lean_ctor_get(v_a_1658_, 0);
lean_inc(v_fst_1659_);
v_snd_1660_ = lean_ctor_get(v_a_1658_, 1);
lean_inc(v_snd_1660_);
lean_dec(v_a_1658_);
v___y_1626_ = v_fst_1647_;
v_fst_1627_ = v_fst_1659_;
v_snd_1628_ = v_snd_1660_;
goto v___jp_1625_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_fst_1647_);
lean_dec(v_snd_1601_);
lean_dec(v_fst_1600_);
lean_dec(v_fst_1596_);
lean_dec(v_fst_1592_);
v_a_1661_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1653_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1653_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v_fst_1647_);
lean_inc_ref(v_head_1590_);
v___x_1669_ = l_Lean_Meta_Grind_ppEqc(v_head_1590_, v_regularEqcs_1624_);
v___x_1670_ = lean_array_push(v_snd_1601_, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v_fst_1600_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_fst_1596_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_fst_1592_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1673_;
v___y_1580_ = v_snd_1648_;
goto _start;
}
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_fst_1600_);
lean_ctor_set(v___x_1692_, 1, v_snd_1601_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_fst_1596_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_fst_1592_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1694_;
goto _start;
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_snd_1601_);
lean_dec(v_fst_1600_);
lean_dec(v_fst_1596_);
lean_dec(v_fst_1592_);
lean_dec_ref(v___y_1580_);
v_a_1696_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1621_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1621_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
v___y_1606_ = v___y_1580_;
goto v___jp_1605_;
}
}
else
{
v___y_1606_ = v___y_1580_;
goto v___jp_1605_;
}
}
else
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1726_; 
lean_del_object(v___x_1603_);
lean_del_object(v___x_1598_);
lean_del_object(v___x_1594_);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v___x_1618_, 0);
lean_dec(v_unused_1727_);
v___x_1705_ = v___x_1618_;
v_isShared_1706_ = v_isSharedCheck_1726_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v___x_1618_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1726_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1707_ = lean_box(0);
lean_inc(v_head_1590_);
v___x_1708_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(v_head_1590_, v___x_1707_);
v___x_1709_ = l_List_isEmpty___redArg(v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec(v_fst_1596_);
v___x_1710_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1711_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0));
v___x_1712_ = lean_array_mk(v___x_1708_);
v___x_1713_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_1714_ = l_Lean_Meta_Grind_ppExprArray(v___x_1710_, v___x_1711_, v___x_1712_, v___x_1713_, v_collapsedProps_1576_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1714_);
v___x_1716_ = v___x_1705_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_fst_1600_);
lean_ctor_set(v___x_1717_, 1, v_snd_1601_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_fst_1592_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1719_;
goto _start;
}
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v___x_1708_);
lean_del_object(v___x_1705_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_fst_1600_);
lean_ctor_set(v___x_1722_, 1, v_snd_1601_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v_fst_1596_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_fst_1592_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1724_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1750_; 
lean_del_object(v___x_1603_);
lean_del_object(v___x_1598_);
lean_del_object(v___x_1594_);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v___x_1617_, 0);
lean_dec(v_unused_1751_);
v___x_1729_ = v___x_1617_;
v_isShared_1730_ = v_isSharedCheck_1750_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v___x_1617_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1750_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1731_ = lean_box(0);
lean_inc(v_head_1590_);
v___x_1732_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(v_head_1590_, v___x_1731_);
v___x_1733_ = l_List_isEmpty___redArg(v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_dec(v_fst_1592_);
v___x_1734_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1735_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3));
v___x_1736_ = lean_array_mk(v___x_1732_);
v___x_1737_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_1738_ = l_Lean_Meta_Grind_ppExprArray(v___x_1734_, v___x_1735_, v___x_1736_, v___x_1737_, v_collapsedProps_1576_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1738_);
v___x_1740_ = v___x_1729_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v_fst_1600_);
lean_ctor_set(v___x_1741_, 1, v_snd_1601_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v_fst_1596_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1740_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1743_;
goto _start;
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v___x_1732_);
lean_del_object(v___x_1729_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_fst_1600_);
lean_ctor_set(v___x_1746_, 1, v_snd_1601_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_fst_1596_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_fst_1592_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1748_;
goto _start;
}
}
}
v___jp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1604_ == 0)
{
v___x_1608_ = v___x_1603_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_fst_1600_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_snd_1601_);
v___x_1608_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1610_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1608_);
v___x_1610_ = v___x_1598_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_fst_1596_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1612_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 1, v___x_1610_);
v___x_1612_ = v___x_1594_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_fst_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
v_as_x27_1577_ = v_tail_1591_;
v_b_1578_ = v___x_1612_;
v___y_1580_ = v___y_1606_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___boxed(lean_object* v_collapsedProps_1757_, lean_object* v_as_x27_1758_, lean_object* v_b_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
uint8_t v_collapsedProps_boxed_1767_; lean_object* v_res_1768_; 
v_collapsedProps_boxed_1767_ = lean_unbox(v_collapsedProps_1757_);
v_res_1768_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_boxed_1767_, v_as_x27_1758_, v_b_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___y_1760_);
lean_dec(v_as_x27_1758_);
return v_res_1768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0(void){
_start:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; double v___x_1771_; lean_object* v_trueEqc_x3f_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1769_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1770_ = 1;
v___x_1771_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v_trueEqc_x3f_1772_ = lean_box(0);
v___x_1773_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1774_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v_trueEqc_x3f_1772_);
lean_ctor_set(v___x_1774_, 2, v___x_1769_);
lean_ctor_set_float(v___x_1774_, sizeof(void*)*3, v___x_1771_);
lean_ctor_set_float(v___x_1774_, sizeof(void*)*3 + 8, v___x_1771_);
lean_ctor_set_uint8(v___x_1774_, sizeof(void*)*3 + 16, v___x_1770_);
return v___x_1774_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2));
v___x_1779_ = l_Lean_MessageData_ofFormat(v___x_1778_);
return v___x_1779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8));
v___x_1792_ = l_Lean_MessageData_ofFormat(v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(uint8_t v_collapsedProps_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = 1;
v___x_1815_ = l_Lean_Meta_Grind_Goal_getEqcs(v_a_1794_, v___x_1802_);
v___x_1816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6));
v___x_1817_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_1793_, v___x_1815_, v___x_1816_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v___x_1815_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v_snd_1821_; lean_object* v_fst_1822_; lean_object* v_fst_1823_; lean_object* v_snd_1824_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v_regularEqcs_1833_; lean_object* v___y_1834_; lean_object* v_fst_1839_; lean_object* v_snd_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v_fst_1819_ = lean_ctor_get(v_a_1818_, 0);
lean_inc(v_fst_1819_);
v_snd_1820_ = lean_ctor_get(v_fst_1819_, 1);
lean_inc(v_snd_1820_);
v_snd_1821_ = lean_ctor_get(v_a_1818_, 1);
lean_inc(v_snd_1821_);
lean_dec(v_a_1818_);
v_fst_1822_ = lean_ctor_get(v_fst_1819_, 0);
lean_inc(v_fst_1822_);
lean_dec(v_fst_1819_);
v_fst_1823_ = lean_ctor_get(v_snd_1820_, 0);
lean_inc(v_fst_1823_);
v_snd_1824_ = lean_ctor_get(v_snd_1820_, 1);
lean_inc(v_snd_1824_);
lean_dec(v_snd_1820_);
v_fst_1839_ = lean_ctor_get(v_snd_1824_, 0);
lean_inc(v_fst_1839_);
v_snd_1840_ = lean_ctor_get(v_snd_1824_, 1);
lean_inc(v_snd_1840_);
lean_dec(v_snd_1824_);
v___x_1841_ = lean_array_get_size(v_snd_1840_);
v___x_1842_ = lean_nat_dec_eq(v___x_1841_, v___x_1801_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1843_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
v___x_1844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9);
v___x_1845_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
lean_ctor_set(v___x_1845_, 2, v_snd_1840_);
v___x_1846_ = lean_array_push(v_fst_1839_, v___x_1845_);
v_regularEqcs_1833_ = v___x_1846_;
v___y_1834_ = v_snd_1821_;
goto v___jp_1832_;
}
else
{
lean_dec(v_snd_1840_);
v_regularEqcs_1833_ = v_fst_1839_;
v___y_1834_ = v_snd_1821_;
goto v___jp_1832_;
}
v___jp_1825_:
{
if (lean_obj_tag(v_fst_1823_) == 1)
{
lean_object* v_val_1828_; lean_object* v___x_1829_; lean_object* v_a_1830_; lean_object* v_snd_1831_; 
v_val_1828_ = lean_ctor_get(v_fst_1823_, 0);
lean_inc(v_val_1828_);
lean_dec_ref_known(v_fst_1823_, 1);
v___x_1829_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_1828_, v___y_1827_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref(v___x_1829_);
v_snd_1831_ = lean_ctor_get(v_a_1830_, 1);
lean_inc(v_snd_1831_);
lean_dec(v_a_1830_);
v___y_1804_ = v___y_1826_;
v___y_1805_ = v_snd_1831_;
goto v___jp_1803_;
}
else
{
lean_dec(v_fst_1823_);
v___y_1804_ = v___y_1826_;
v___y_1805_ = v___y_1827_;
goto v___jp_1803_;
}
}
v___jp_1832_:
{
if (lean_obj_tag(v_fst_1822_) == 1)
{
lean_object* v_val_1835_; lean_object* v___x_1836_; lean_object* v_a_1837_; lean_object* v_snd_1838_; 
v_val_1835_ = lean_ctor_get(v_fst_1822_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v_fst_1822_, 1);
v___x_1836_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_1835_, v___y_1834_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1836_);
v_snd_1838_ = lean_ctor_get(v_a_1837_, 1);
lean_inc(v_snd_1838_);
lean_dec(v_a_1837_);
v___y_1826_ = v_regularEqcs_1833_;
v___y_1827_ = v_snd_1838_;
goto v___jp_1825_;
}
else
{
lean_dec(v_fst_1822_);
v___y_1826_ = v_regularEqcs_1833_;
v___y_1827_ = v___y_1834_;
goto v___jp_1825_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1817_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1817_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
v___jp_1803_:
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_array_get_size(v___y_1804_);
v___x_1807_ = lean_nat_dec_eq(v___x_1806_, v___x_1801_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3);
v___x_1810_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
lean_ctor_set(v___x_1810_, 2, v___y_1804_);
v___x_1811_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_1810_, v___y_1805_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec_ref(v___y_1804_);
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___y_1805_);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___boxed(lean_object* v_collapsedProps_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
uint8_t v_collapsedProps_boxed_1863_; lean_object* v_res_1864_; 
v_collapsedProps_boxed_1863_ = lean_unbox(v_collapsedProps_1855_);
v_res_1864_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(v_collapsedProps_boxed_1863_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec_ref(v_a_1856_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___redArg(v_x_1865_, v_x_1866_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___boxed(lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(v_x_1875_, v_x_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v___y_1877_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_x_1885_, v_x_1886_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___boxed(lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(v_x_1895_, v_x_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec_ref(v___y_1897_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(uint8_t v_collapsedProps_1905_, lean_object* v_as_1906_, lean_object* v_as_x27_1907_, lean_object* v_b_1908_, lean_object* v_a_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_1905_, v_as_x27_1907_, v_b_1908_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___boxed(lean_object* v_collapsedProps_1918_, lean_object* v_as_1919_, lean_object* v_as_x27_1920_, lean_object* v_b_1921_, lean_object* v_a_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v_collapsedProps_boxed_1930_; lean_object* v_res_1931_; 
v_collapsedProps_boxed_1930_ = lean_unbox(v_collapsedProps_1918_);
v_res_1931_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(v_collapsedProps_boxed_1930_, v_as_1919_, v_as_x27_1920_, v_b_1921_, v_a_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec_ref(v___y_1923_);
lean_dec(v_as_x27_1920_);
lean_dec(v_as_1919_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
if (lean_obj_tag(v_a_1932_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = l_List_reverse___redArg(v_a_1933_);
return v___x_1934_;
}
else
{
lean_object* v_head_1935_; lean_object* v_tail_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1945_; 
v_head_1935_ = lean_ctor_get(v_a_1932_, 0);
v_tail_1936_ = lean_ctor_get(v_a_1932_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1932_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1938_ = v_a_1932_;
v_isShared_1939_ = v_isSharedCheck_1945_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_tail_1936_);
lean_inc(v_head_1935_);
lean_dec(v_a_1932_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1945_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = l_Lean_Meta_Grind_ppPattern(v_head_1935_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v_a_1933_);
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_a_1933_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_a_1932_ = v_tail_1936_;
v_a_1933_ = v___x_1942_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
if (lean_obj_tag(v_a_1946_) == 0)
{
lean_object* v___x_1948_; 
v___x_1948_ = l_List_reverse___redArg(v_a_1947_);
return v___x_1948_;
}
else
{
lean_object* v_head_1949_; lean_object* v_tail_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1958_; 
v_head_1949_ = lean_ctor_get(v_a_1946_, 0);
v_tail_1950_ = lean_ctor_get(v_a_1946_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_a_1946_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1952_ = v_a_1946_;
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_tail_1950_);
lean_inc(v_head_1949_);
lean_dec(v_a_1946_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v_a_1947_);
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_head_1949_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_a_1947_);
v___x_1955_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
v_a_1946_ = v_tail_1950_;
v_a_1947_ = v___x_1955_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0));
v___x_1961_ = l_Lean_stringToMessageData(v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4(void){
_start:
{
lean_object* v___x_1965_; uint8_t v___x_1966_; double v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1965_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1966_ = 1;
v___x_1967_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1968_ = lean_box(0);
v___x_1969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3));
v___x_1970_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v___x_1968_);
lean_ctor_set(v___x_1970_, 2, v___x_1965_);
lean_ctor_set_float(v___x_1970_, sizeof(void*)*3, v___x_1967_);
lean_ctor_set_float(v___x_1970_, sizeof(void*)*3 + 8, v___x_1967_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*3 + 16, v___x_1966_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(lean_object* v_thm_1971_){
_start:
{
lean_object* v_patterns_1973_; lean_object* v_origin_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v_m_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_patterns_1973_ = lean_ctor_get(v_thm_1971_, 3);
lean_inc(v_patterns_1973_);
v_origin_1974_ = lean_ctor_get(v_thm_1971_, 5);
lean_inc_ref(v_origin_1974_);
lean_dec_ref(v_thm_1971_);
v___x_1975_ = l_Lean_Meta_Grind_Origin_pp(v_origin_1974_);
v___x_1976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = lean_box(0);
v___x_1979_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(v_patterns_1973_, v___x_1978_);
v___x_1980_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(v___x_1979_, v___x_1978_);
v___x_1981_ = l_Lean_MessageData_ofList(v___x_1980_);
v_m_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_1982_, 0, v___x_1977_);
lean_ctor_set(v_m_1982_, 1, v___x_1981_);
v___x_1983_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4);
v___x_1984_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1985_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v_m_1982_);
lean_ctor_set(v___x_1985_, 2, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___boxed(lean_object* v_thm_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_thm_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(lean_object* v_thm_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_thm_1990_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___boxed(lean_object* v_thm_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(v_thm_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(size_t v_sz_2004_, size_t v_i_2005_, lean_object* v_bs_2006_, lean_object* v___y_2007_){
_start:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_usize_dec_lt(v_i_2005_, v_sz_2004_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v_bs_2006_);
lean_ctor_set(v___x_2010_, 1, v___y_2007_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
return v___x_2011_;
}
else
{
lean_object* v_v_2012_; lean_object* v___x_2013_; 
v_v_2012_ = lean_array_uget_borrowed(v_bs_2006_, v_i_2005_);
lean_inc(v_v_2012_);
v___x_2013_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_v_2012_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; lean_object* v_bs_x27_2016_; size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = lean_unsigned_to_nat(0u);
v_bs_x27_2016_ = lean_array_uset(v_bs_2006_, v_i_2005_, v___x_2015_);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_2005_, v___x_2017_);
v___x_2019_ = lean_array_uset(v_bs_x27_2016_, v_i_2005_, v_a_2014_);
v_i_2005_ = v___x_2018_;
v_bs_2006_ = v___x_2019_;
goto _start;
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v___y_2007_);
lean_dec_ref(v_bs_2006_);
v_a_2021_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2013_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2013_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg___boxed(lean_object* v_sz_2029_, lean_object* v_i_2030_, lean_object* v_bs_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
size_t v_sz_boxed_2034_; size_t v_i_boxed_2035_; lean_object* v_res_2036_; 
v_sz_boxed_2034_ = lean_unbox_usize(v_sz_2029_);
lean_dec(v_sz_2029_);
v_i_boxed_2035_ = lean_unbox_usize(v_i_2030_);
lean_dec(v_i_2030_);
v_res_2036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_boxed_2034_, v_i_boxed_2035_, v_bs_2031_, v___y_2032_);
return v_res_2036_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2(void){
_start:
{
lean_object* v___x_2040_; uint8_t v___x_2041_; double v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2040_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2041_ = 1;
v___x_2042_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2043_ = lean_box(0);
v___x_2044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1));
v___x_2045_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v___x_2043_);
lean_ctor_set(v___x_2045_, 2, v___x_2040_);
lean_ctor_set_float(v___x_2045_, sizeof(void*)*3, v___x_2042_);
lean_ctor_set_float(v___x_2045_, sizeof(void*)*3 + 8, v___x_2042_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*3 + 16, v___x_2041_);
return v___x_2045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4));
v___x_2050_ = l_Lean_MessageData_ofFormat(v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_toGoalState_2058_; lean_object* v_ematch_2059_; lean_object* v_thms_2060_; lean_object* v_newThms_2061_; lean_object* v___x_2062_; size_t v_sz_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v_toGoalState_2058_ = lean_ctor_get(v_a_2051_, 0);
v_ematch_2059_ = lean_ctor_get(v_toGoalState_2058_, 12);
v_thms_2060_ = lean_ctor_get(v_ematch_2059_, 2);
v_newThms_2061_ = lean_ctor_get(v_ematch_2059_, 3);
v___x_2062_ = l_Lean_PersistentArray_toArray___redArg(v_thms_2060_);
v_sz_2063_ = lean_array_size(v___x_2062_);
v___x_2064_ = ((size_t)0ULL);
v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2063_, v___x_2064_, v___x_2062_, v_a_2052_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2069_; size_t v_sz_2070_; lean_object* v___x_2071_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v_fst_2067_ = lean_ctor_get(v_a_2066_, 0);
lean_inc(v_fst_2067_);
v_snd_2068_ = lean_ctor_get(v_a_2066_, 1);
lean_inc(v_snd_2068_);
lean_dec(v_a_2066_);
v___x_2069_ = l_Lean_PersistentArray_toArray___redArg(v_newThms_2061_);
v_sz_2070_ = lean_array_size(v___x_2069_);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2070_, v___x_2064_, v___x_2069_, v_snd_2068_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2097_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2097_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2097_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_fst_2076_; lean_object* v_snd_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2096_; 
v_fst_2076_ = lean_ctor_get(v_a_2072_, 0);
v_snd_2077_ = lean_ctor_get(v_a_2072_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_a_2072_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2079_ = v_a_2072_;
v_isShared_2080_ = v_isSharedCheck_2096_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snd_2077_);
lean_inc(v_fst_2076_);
lean_dec(v_a_2072_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2096_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2081_ = l_Array_append___redArg(v_fst_2067_, v_fst_2076_);
lean_dec(v_fst_2076_);
v___x_2082_ = lean_array_get_size(v___x_2081_);
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = lean_nat_dec_eq(v___x_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_del_object(v___x_2079_);
lean_del_object(v___x_2074_);
v___x_2085_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2);
v___x_2086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5);
v___x_2087_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
lean_ctor_set(v___x_2087_, 2, v___x_2081_);
v___x_2088_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2087_, v_snd_2077_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_dec_ref(v___x_2081_);
v___x_2089_ = lean_box(0);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2089_);
v___x_2091_ = v___x_2079_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_snd_2077_);
v___x_2091_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2091_);
v___x_2093_ = v___x_2074_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_fst_2067_);
v_a_2098_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2071_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2071_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_a_2106_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2065_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2065_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___boxed(lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_a_2114_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(size_t v_sz_2122_, size_t v_i_2123_, lean_object* v_bs_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2122_, v_i_2123_, v_bs_2124_, v___y_2126_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___boxed(lean_object* v_sz_2133_, lean_object* v_i_2134_, lean_object* v_bs_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
size_t v_sz_boxed_2143_; size_t v_i_boxed_2144_; lean_object* v_res_2145_; 
v_sz_boxed_2143_ = lean_unbox_usize(v_sz_2133_);
lean_dec(v_sz_2133_);
v_i_boxed_2144_ = lean_unbox_usize(v_i_2134_);
lean_dec(v_i_2134_);
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(v_sz_boxed_2143_, v_i_boxed_2144_, v_bs_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec_ref(v___y_2136_);
return v_res_2145_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(lean_object* v_x_2146_){
_start:
{
uint8_t v___x_2147_; 
v___x_2147_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg___boxed(lean_object* v_x_2148_){
_start:
{
uint8_t v_res_2149_; lean_object* v_r_2150_; 
v_res_2149_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(v_x_2148_);
lean_dec_ref(v_x_2148_);
v_r_2150_ = lean_box(v_res_2149_);
return v_r_2150_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(lean_object* v_00_u03b2_2151_, lean_object* v_x_2152_){
_start:
{
uint8_t v___x_2153_; 
v___x_2153_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___boxed(lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_){
_start:
{
uint8_t v_res_2156_; lean_object* v_r_2157_; 
v_res_2156_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(v_00_u03b2_2154_, v_x_2155_);
lean_dec_ref(v_x_2155_);
v_r_2157_ = lean_box(v_res_2156_);
return v_r_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(lean_object* v_as_2162_, size_t v_sz_2163_, size_t v_i_2164_, lean_object* v_b_2165_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_usize_dec_lt(v_i_2164_, v_sz_2163_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_b_2165_);
return v___x_2168_;
}
else
{
lean_object* v_a_2169_; lean_object* v_fst_2170_; lean_object* v_snd_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2212_; 
v_a_2169_ = lean_array_uget(v_as_2162_, v_i_2164_);
v_fst_2170_ = lean_ctor_get(v_a_2169_, 0);
v_snd_2171_ = lean_ctor_get(v_a_2169_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_a_2169_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2173_ = v_a_2169_;
v_isShared_2174_ = v_isSharedCheck_2212_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_snd_2171_);
lean_inc(v_fst_2170_);
lean_dec(v_a_2169_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2212_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; double v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_num_2181_; lean_object* v_den_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2211_; 
v___x_2175_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1));
v___x_2177_ = lean_box(0);
v___x_2178_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2179_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2180_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2180_, 0, v___x_2176_);
lean_ctor_set(v___x_2180_, 1, v___x_2177_);
lean_ctor_set(v___x_2180_, 2, v___x_2179_);
lean_ctor_set_float(v___x_2180_, sizeof(void*)*3, v___x_2178_);
lean_ctor_set_float(v___x_2180_, sizeof(void*)*3 + 8, v___x_2178_);
lean_ctor_set_uint8(v___x_2180_, sizeof(void*)*3 + 16, v___x_2167_);
v_num_2181_ = lean_ctor_get(v_snd_2171_, 0);
v_den_2182_ = lean_ctor_get(v_snd_2171_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_snd_2171_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2184_ = v_snd_2171_;
v_isShared_2185_ = v_isSharedCheck_2211_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_den_2182_);
lean_inc(v_num_2181_);
lean_dec(v_snd_2171_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2211_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2186_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2170_);
v___x_2187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9);
if (v_isShared_2185_ == 0)
{
lean_ctor_set_tag(v___x_2184_, 7);
lean_ctor_set(v___x_2184_, 1, v___x_2187_);
lean_ctor_set(v___x_2184_, 0, v___x_2186_);
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___y_2191_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = lean_nat_dec_eq(v_den_2182_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2204_ = l_Int_repr(v_num_2181_);
lean_dec(v_num_2181_);
v___x_2205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2));
v___x_2206_ = lean_string_append(v___x_2204_, v___x_2205_);
v___x_2207_ = l_Nat_reprFast(v_den_2182_);
v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
lean_dec_ref(v___x_2207_);
v___y_2191_ = v___x_2208_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2209_; 
lean_dec(v_den_2182_);
v___x_2209_ = l_Int_repr(v_num_2181_);
lean_dec(v_num_2181_);
v___y_2191_ = v___x_2209_;
goto v___jp_2190_;
}
v___jp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___y_2191_);
v___x_2193_ = l_Lean_MessageData_ofFormat(v___x_2192_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 7);
lean_ctor_set(v___x_2173_, 1, v___x_2193_);
lean_ctor_set(v___x_2173_, 0, v___x_2189_);
v___x_2195_ = v___x_2173_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; 
v___x_2196_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2180_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
lean_ctor_set(v___x_2196_, 2, v___x_2175_);
v___x_2197_ = lean_array_push(v_b_2165_, v___x_2196_);
v___x_2198_ = ((size_t)1ULL);
v___x_2199_ = lean_usize_add(v_i_2164_, v___x_2198_);
v_i_2164_ = v___x_2199_;
v_b_2165_ = v___x_2197_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___boxed(lean_object* v_as_2213_, lean_object* v_sz_2214_, lean_object* v_i_2215_, lean_object* v_b_2216_, lean_object* v___y_2217_){
_start:
{
size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2214_);
lean_dec(v_sz_2214_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2215_);
lean_dec(v_i_2215_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_2213_, v_sz_boxed_2218_, v_i_boxed_2219_, v_b_2216_);
lean_dec_ref(v_as_2213_);
return v_res_2220_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2(void){
_start:
{
lean_object* v___x_2224_; uint8_t v___x_2225_; double v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2224_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2225_ = 1;
v___x_2226_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2227_ = lean_box(0);
v___x_2228_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1));
v___x_2229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2227_);
lean_ctor_set(v___x_2229_, 2, v___x_2224_);
lean_ctor_set_float(v___x_2229_, sizeof(void*)*3, v___x_2226_);
lean_ctor_set_float(v___x_2229_, sizeof(void*)*3 + 8, v___x_2226_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 16, v___x_2225_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4));
v___x_2234_ = l_Lean_MessageData_ofFormat(v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(lean_object* v_goal_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2242_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2241_, v_goal_2235_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2298_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2298_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2298_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v_varMap_2247_; uint8_t v___x_2248_; 
v_varMap_2247_ = lean_ctor_get(v_a_2243_, 1);
lean_inc_ref(v_varMap_2247_);
lean_dec(v_a_2243_);
v___x_2248_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_varMap_2247_);
lean_dec_ref(v_varMap_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_del_object(v___x_2245_);
v___x_2249_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2285_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2285_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2285_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2254_ = lean_array_get_size(v_a_2250_);
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = lean_nat_dec_eq(v___x_2254_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; size_t v_sz_2258_; size_t v___x_2259_; lean_object* v___x_2260_; 
lean_del_object(v___x_2252_);
v___x_2257_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v_sz_2258_ = lean_array_size(v_a_2250_);
v___x_2259_ = ((size_t)0ULL);
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_a_2250_, v_sz_2258_, v___x_2259_, v___x_2257_);
lean_dec(v_a_2250_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2272_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2272_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2265_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2);
v___x_2266_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5);
v___x_2267_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
lean_ctor_set(v___x_2267_, 2, v_a_2261_);
v___x_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2268_);
v___x_2270_ = v___x_2263_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2260_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2260_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
lean_dec(v_a_2250_);
v___x_2281_ = lean_box(0);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2281_);
v___x_2283_ = v___x_2252_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
v_a_2286_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2249_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2249_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
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
lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2294_ = lean_box(0);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2294_);
v___x_2296_ = v___x_2245_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2311_; 
v_a_2299_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2301_ = v___x_2242_;
v_isShared_2302_ = v_isSharedCheck_2311_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2242_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2311_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_ref_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v_ref_2303_ = lean_ctor_get(v_a_2238_, 5);
v___x_2304_ = lean_io_error_to_string(v_a_2299_);
v___x_2305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
v___x_2306_ = l_Lean_MessageData_ofFormat(v___x_2305_);
lean_inc(v_ref_2303_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v_ref_2303_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2307_);
v___x_2309_ = v___x_2301_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___boxed(lean_object* v_goal_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(v_goal_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec_ref(v_goal_2312_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(lean_object* v_as_2319_, size_t v_sz_2320_, size_t v_i_2321_, lean_object* v_b_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_2319_, v_sz_2320_, v_i_2321_, v_b_2322_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___boxed(lean_object* v_as_2329_, lean_object* v_sz_2330_, lean_object* v_i_2331_, lean_object* v_b_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
size_t v_sz_boxed_2338_; size_t v_i_boxed_2339_; lean_object* v_res_2340_; 
v_sz_boxed_2338_ = lean_unbox_usize(v_sz_2330_);
lean_dec(v_sz_2330_);
v_i_boxed_2339_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_res_2340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(v_as_2329_, v_sz_boxed_2338_, v_i_boxed_2339_, v_b_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec_ref(v_as_2329_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(v_a_2341_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2360_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2360_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2360_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
if (lean_obj_tag(v_a_2349_) == 1)
{
lean_object* v_val_2353_; lean_object* v___x_2354_; 
lean_del_object(v___x_2351_);
v_val_2353_ = lean_ctor_get(v_a_2349_, 0);
lean_inc(v_val_2353_);
lean_dec_ref_known(v_a_2349_, 1);
v___x_2354_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2353_, v_a_2342_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
lean_dec(v_a_2349_);
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v_a_2342_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2356_);
v___x_2358_ = v___x_2351_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v_a_2342_);
v_a_2361_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2348_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2348_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat___boxed(lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec_ref(v_a_2369_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(v_a_2377_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2396_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2396_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2396_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
if (lean_obj_tag(v_a_2385_) == 1)
{
lean_object* v_val_2389_; lean_object* v___x_2390_; 
lean_del_object(v___x_2387_);
v_val_2389_ = lean_ctor_get(v_a_2385_, 0);
lean_inc(v_val_2389_);
lean_dec_ref_known(v_a_2385_, 1);
v___x_2390_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2389_, v_a_2378_);
return v___x_2390_;
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
lean_dec(v_a_2385_);
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v_a_2378_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2392_);
v___x_2394_ = v___x_2387_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_a_2378_);
v_a_2397_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2384_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2384_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing___boxed(lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec_ref(v_a_2405_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_a_2413_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2432_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
if (lean_obj_tag(v_a_2421_) == 1)
{
lean_object* v_val_2425_; lean_object* v___x_2426_; 
lean_del_object(v___x_2423_);
v_val_2425_ = lean_ctor_get(v_a_2421_, 0);
lean_inc(v_val_2425_);
lean_dec_ref_known(v_a_2421_, 1);
v___x_2426_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2425_, v_a_2414_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_dec(v_a_2421_);
v___x_2427_ = lean_box(0);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v_a_2414_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2428_);
v___x_2430_ = v___x_2423_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v_a_2414_);
v_a_2433_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2420_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2420_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith___boxed(lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec_ref(v_a_2441_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_Meta_Grind_AC_pp_x3f(v_a_2449_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2468_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2468_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2468_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
if (lean_obj_tag(v_a_2457_) == 1)
{
lean_object* v_val_2461_; lean_object* v___x_2462_; 
lean_del_object(v___x_2459_);
v_val_2461_ = lean_ctor_get(v_a_2457_, 0);
lean_inc(v_val_2461_);
lean_dec_ref_known(v_a_2457_, 1);
v___x_2462_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2461_, v_a_2450_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_dec(v_a_2457_);
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v_a_2450_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2464_);
v___x_2466_ = v___x_2459_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_a_2450_);
v_a_2469_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2456_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2456_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC___boxed(lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec_ref(v_a_2477_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(lean_object* v_a_2485_, lean_object* v_as_2486_, size_t v_i_2487_, size_t v_stop_2488_, lean_object* v_b_2489_){
_start:
{
lean_object* v___y_2491_; uint8_t v___x_2495_; 
v___x_2495_ = lean_usize_dec_eq(v_i_2487_, v_stop_2488_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_array_uget_borrowed(v_as_2486_, v_i_2487_);
v___x_2497_ = l_Lean_Meta_Grind_Goal_getENode_x3f(v_a_2485_, v___x_2496_);
if (lean_obj_tag(v___x_2497_) == 1)
{
lean_object* v_val_2498_; lean_object* v_generation_2499_; uint8_t v___x_2500_; 
v_val_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_val_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v_generation_2499_ = lean_ctor_get(v_val_2498_, 8);
lean_inc(v_generation_2499_);
lean_dec(v_val_2498_);
v___x_2500_ = lean_nat_dec_le(v_b_2489_, v_generation_2499_);
if (v___x_2500_ == 0)
{
lean_dec(v_generation_2499_);
v___y_2491_ = v_b_2489_;
goto v___jp_2490_;
}
else
{
lean_dec(v_b_2489_);
v___y_2491_ = v_generation_2499_;
goto v___jp_2490_;
}
}
else
{
lean_dec(v___x_2497_);
v___y_2491_ = v_b_2489_;
goto v___jp_2490_;
}
}
else
{
return v_b_2489_;
}
v___jp_2490_:
{
size_t v___x_2492_; size_t v___x_2493_; 
v___x_2492_ = ((size_t)1ULL);
v___x_2493_ = lean_usize_add(v_i_2487_, v___x_2492_);
v_i_2487_ = v___x_2493_;
v_b_2489_ = v___y_2491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1___boxed(lean_object* v_a_2501_, lean_object* v_as_2502_, lean_object* v_i_2503_, lean_object* v_stop_2504_, lean_object* v_b_2505_){
_start:
{
size_t v_i_boxed_2506_; size_t v_stop_boxed_2507_; lean_object* v_res_2508_; 
v_i_boxed_2506_ = lean_unbox_usize(v_i_2503_);
lean_dec(v_i_2503_);
v_stop_boxed_2507_ = lean_unbox_usize(v_stop_2504_);
lean_dec(v_stop_2504_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2501_, v_as_2502_, v_i_boxed_2506_, v_stop_boxed_2507_, v_b_2505_);
lean_dec_ref(v_as_2502_);
lean_dec_ref(v_a_2501_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(lean_object* v_a_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
lean_object* v_cs_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_cs_2512_ = lean_ctor_get(v_x_2510_, 0);
v___x_2513_ = lean_unsigned_to_nat(0u);
v___x_2514_ = lean_array_get_size(v_cs_2512_);
v___x_2515_ = lean_nat_dec_lt(v___x_2513_, v___x_2514_);
if (v___x_2515_ == 0)
{
return v_x_2511_;
}
else
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_nat_dec_le(v___x_2514_, v___x_2514_);
if (v___x_2516_ == 0)
{
if (v___x_2515_ == 0)
{
return v_x_2511_;
}
else
{
size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = ((size_t)0ULL);
v___x_2518_ = lean_usize_of_nat(v___x_2514_);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2509_, v_cs_2512_, v___x_2517_, v___x_2518_, v_x_2511_);
return v___x_2519_;
}
}
else
{
size_t v___x_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = lean_usize_of_nat(v___x_2514_);
v___x_2522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2509_, v_cs_2512_, v___x_2520_, v___x_2521_, v_x_2511_);
return v___x_2522_;
}
}
}
else
{
lean_object* v_vs_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_vs_2523_ = lean_ctor_get(v_x_2510_, 0);
v___x_2524_ = lean_unsigned_to_nat(0u);
v___x_2525_ = lean_array_get_size(v_vs_2523_);
v___x_2526_ = lean_nat_dec_lt(v___x_2524_, v___x_2525_);
if (v___x_2526_ == 0)
{
return v_x_2511_;
}
else
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_nat_dec_le(v___x_2525_, v___x_2525_);
if (v___x_2527_ == 0)
{
if (v___x_2526_ == 0)
{
return v_x_2511_;
}
else
{
size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = lean_usize_of_nat(v___x_2525_);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2509_, v_vs_2523_, v___x_2528_, v___x_2529_, v_x_2511_);
return v___x_2530_;
}
}
else
{
size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = ((size_t)0ULL);
v___x_2532_ = lean_usize_of_nat(v___x_2525_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2509_, v_vs_2523_, v___x_2531_, v___x_2532_, v_x_2511_);
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(lean_object* v_a_2534_, lean_object* v_as_2535_, size_t v_i_2536_, size_t v_stop_2537_, lean_object* v_b_2538_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_usize_dec_eq(v_i_2536_, v_stop_2537_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; size_t v___x_2542_; size_t v___x_2543_; 
v___x_2540_ = lean_array_uget_borrowed(v_as_2535_, v_i_2536_);
v___x_2541_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2534_, v___x_2540_, v_b_2538_);
v___x_2542_ = ((size_t)1ULL);
v___x_2543_ = lean_usize_add(v_i_2536_, v___x_2542_);
v_i_2536_ = v___x_2543_;
v_b_2538_ = v___x_2541_;
goto _start;
}
else
{
return v_b_2538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1___boxed(lean_object* v_a_2545_, lean_object* v_as_2546_, lean_object* v_i_2547_, lean_object* v_stop_2548_, lean_object* v_b_2549_){
_start:
{
size_t v_i_boxed_2550_; size_t v_stop_boxed_2551_; lean_object* v_res_2552_; 
v_i_boxed_2550_ = lean_unbox_usize(v_i_2547_);
lean_dec(v_i_2547_);
v_stop_boxed_2551_ = lean_unbox_usize(v_stop_2548_);
lean_dec(v_stop_2548_);
v_res_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2545_, v_as_2546_, v_i_boxed_2550_, v_stop_boxed_2551_, v_b_2549_);
lean_dec_ref(v_as_2546_);
lean_dec_ref(v_a_2545_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2___boxed(lean_object* v_a_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2553_, v_x_2554_, v_x_2555_);
lean_dec_ref(v_x_2554_);
lean_dec_ref(v_a_2553_);
return v_res_2556_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(lean_object* v_a_2558_, lean_object* v_x_2559_, size_t v_x_2560_, size_t v_x_2561_, lean_object* v_x_2562_){
_start:
{
if (lean_obj_tag(v_x_2559_) == 0)
{
lean_object* v_cs_2563_; lean_object* v___x_2564_; size_t v___x_2565_; lean_object* v_j_2566_; lean_object* v___x_2567_; size_t v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; size_t v___x_2572_; size_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v_cs_2563_ = lean_ctor_get(v_x_2559_, 0);
v___x_2564_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___closed__0);
v___x_2565_ = lean_usize_shift_right(v_x_2560_, v_x_2561_);
v_j_2566_ = lean_usize_to_nat(v___x_2565_);
v___x_2567_ = lean_array_get_borrowed(v___x_2564_, v_cs_2563_, v_j_2566_);
v___x_2568_ = ((size_t)1ULL);
v___x_2569_ = lean_usize_shift_left(v___x_2568_, v_x_2561_);
v___x_2570_ = lean_usize_sub(v___x_2569_, v___x_2568_);
v___x_2571_ = lean_usize_land(v_x_2560_, v___x_2570_);
v___x_2572_ = ((size_t)5ULL);
v___x_2573_ = lean_usize_sub(v_x_2561_, v___x_2572_);
v___x_2574_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2558_, v___x_2567_, v___x_2571_, v___x_2573_, v_x_2562_);
v___x_2575_ = lean_unsigned_to_nat(1u);
v___x_2576_ = lean_nat_add(v_j_2566_, v___x_2575_);
lean_dec(v_j_2566_);
v___x_2577_ = lean_array_get_size(v_cs_2563_);
v___x_2578_ = lean_nat_dec_lt(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_dec(v___x_2576_);
return v___x_2574_;
}
else
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_nat_dec_le(v___x_2577_, v___x_2577_);
if (v___x_2579_ == 0)
{
if (v___x_2578_ == 0)
{
lean_dec(v___x_2576_);
return v___x_2574_;
}
else
{
size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_usize_of_nat(v___x_2576_);
lean_dec(v___x_2576_);
v___x_2581_ = lean_usize_of_nat(v___x_2577_);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2558_, v_cs_2563_, v___x_2580_, v___x_2581_, v___x_2574_);
return v___x_2582_;
}
}
else
{
size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_usize_of_nat(v___x_2576_);
lean_dec(v___x_2576_);
v___x_2584_ = lean_usize_of_nat(v___x_2577_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2558_, v_cs_2563_, v___x_2583_, v___x_2584_, v___x_2574_);
return v___x_2585_;
}
}
}
else
{
lean_object* v_vs_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v_vs_2586_ = lean_ctor_get(v_x_2559_, 0);
v___x_2587_ = lean_usize_to_nat(v_x_2560_);
v___x_2588_ = lean_array_get_size(v_vs_2586_);
v___x_2589_ = lean_nat_dec_lt(v___x_2587_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_dec(v___x_2587_);
return v_x_2562_;
}
else
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_nat_dec_le(v___x_2588_, v___x_2588_);
if (v___x_2590_ == 0)
{
if (v___x_2589_ == 0)
{
lean_dec(v___x_2587_);
return v_x_2562_;
}
else
{
size_t v___x_2591_; size_t v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_usize_of_nat(v___x_2587_);
lean_dec(v___x_2587_);
v___x_2592_ = lean_usize_of_nat(v___x_2588_);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2558_, v_vs_2586_, v___x_2591_, v___x_2592_, v_x_2562_);
return v___x_2593_;
}
}
else
{
size_t v___x_2594_; size_t v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_usize_of_nat(v___x_2587_);
lean_dec(v___x_2587_);
v___x_2595_ = lean_usize_of_nat(v___x_2588_);
v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2558_, v_vs_2586_, v___x_2594_, v___x_2595_, v_x_2562_);
return v___x_2596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___boxed(lean_object* v_a_2597_, lean_object* v_x_2598_, lean_object* v_x_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_){
_start:
{
size_t v_x_5395__boxed_2602_; size_t v_x_5396__boxed_2603_; lean_object* v_res_2604_; 
v_x_5395__boxed_2602_ = lean_unbox_usize(v_x_2599_);
lean_dec(v_x_2599_);
v_x_5396__boxed_2603_ = lean_unbox_usize(v_x_2600_);
lean_dec(v_x_2600_);
v_res_2604_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2597_, v_x_2598_, v_x_5395__boxed_2602_, v_x_5396__boxed_2603_, v_x_2601_);
lean_dec_ref(v_x_2598_);
lean_dec_ref(v_a_2597_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(lean_object* v_a_2605_, lean_object* v_t_2606_, lean_object* v_init_2607_, lean_object* v_start_2608_){
_start:
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_nat_dec_eq(v_start_2608_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v_root_2611_; lean_object* v_tail_2612_; size_t v_shift_2613_; lean_object* v_tailOff_2614_; uint8_t v___x_2615_; 
v_root_2611_ = lean_ctor_get(v_t_2606_, 0);
v_tail_2612_ = lean_ctor_get(v_t_2606_, 1);
v_shift_2613_ = lean_ctor_get_usize(v_t_2606_, 4);
v_tailOff_2614_ = lean_ctor_get(v_t_2606_, 3);
v___x_2615_ = lean_nat_dec_le(v_tailOff_2614_, v_start_2608_);
if (v___x_2615_ == 0)
{
size_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2616_ = lean_usize_of_nat(v_start_2608_);
v___x_2617_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2605_, v_root_2611_, v___x_2616_, v_shift_2613_, v_init_2607_);
v___x_2618_ = lean_array_get_size(v_tail_2612_);
v___x_2619_ = lean_nat_dec_lt(v___x_2609_, v___x_2618_);
if (v___x_2619_ == 0)
{
return v___x_2617_;
}
else
{
uint8_t v___x_2620_; 
v___x_2620_ = lean_nat_dec_le(v___x_2618_, v___x_2618_);
if (v___x_2620_ == 0)
{
if (v___x_2619_ == 0)
{
return v___x_2617_;
}
else
{
size_t v___x_2621_; size_t v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = ((size_t)0ULL);
v___x_2622_ = lean_usize_of_nat(v___x_2618_);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2612_, v___x_2621_, v___x_2622_, v___x_2617_);
return v___x_2623_;
}
}
else
{
size_t v___x_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = ((size_t)0ULL);
v___x_2625_ = lean_usize_of_nat(v___x_2618_);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2612_, v___x_2624_, v___x_2625_, v___x_2617_);
return v___x_2626_;
}
}
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2627_ = lean_nat_sub(v_start_2608_, v_tailOff_2614_);
v___x_2628_ = lean_array_get_size(v_tail_2612_);
v___x_2629_ = lean_nat_dec_lt(v___x_2627_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_dec(v___x_2627_);
return v_init_2607_;
}
else
{
uint8_t v___x_2630_; 
v___x_2630_ = lean_nat_dec_le(v___x_2628_, v___x_2628_);
if (v___x_2630_ == 0)
{
if (v___x_2629_ == 0)
{
lean_dec(v___x_2627_);
return v_init_2607_;
}
else
{
size_t v___x_2631_; size_t v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = lean_usize_of_nat(v___x_2627_);
lean_dec(v___x_2627_);
v___x_2632_ = lean_usize_of_nat(v___x_2628_);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2612_, v___x_2631_, v___x_2632_, v_init_2607_);
return v___x_2633_;
}
}
else
{
size_t v___x_2634_; size_t v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_usize_of_nat(v___x_2627_);
lean_dec(v___x_2627_);
v___x_2635_ = lean_usize_of_nat(v___x_2628_);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2612_, v___x_2634_, v___x_2635_, v_init_2607_);
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_root_2637_; lean_object* v_tail_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v_root_2637_ = lean_ctor_get(v_t_2606_, 0);
v_tail_2638_ = lean_ctor_get(v_t_2606_, 1);
v___x_2639_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2605_, v_root_2637_, v_init_2607_);
v___x_2640_ = lean_array_get_size(v_tail_2638_);
v___x_2641_ = lean_nat_dec_lt(v___x_2609_, v___x_2640_);
if (v___x_2641_ == 0)
{
return v___x_2639_;
}
else
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_nat_dec_le(v___x_2640_, v___x_2640_);
if (v___x_2642_ == 0)
{
if (v___x_2641_ == 0)
{
return v___x_2639_;
}
else
{
size_t v___x_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = lean_usize_of_nat(v___x_2640_);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2638_, v___x_2643_, v___x_2644_, v___x_2639_);
return v___x_2645_;
}
}
else
{
size_t v___x_2646_; size_t v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = lean_usize_of_nat(v___x_2640_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2638_, v___x_2646_, v___x_2647_, v___x_2639_);
return v___x_2648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0___boxed(lean_object* v_a_2649_, lean_object* v_t_2650_, lean_object* v_init_2651_, lean_object* v_start_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_2649_, v_t_2650_, v_init_2651_, v_start_2652_);
lean_dec(v_start_2652_);
lean_dec_ref(v_t_2650_);
lean_dec_ref(v_a_2649_);
return v_res_2653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2(void){
_start:
{
lean_object* v___x_2657_; uint8_t v___x_2658_; double v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2657_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2658_ = 1;
v___x_2659_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2660_ = lean_box(0);
v___x_2661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1));
v___x_2662_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v___x_2660_);
lean_ctor_set(v___x_2662_, 2, v___x_2657_);
lean_ctor_set_float(v___x_2662_, sizeof(void*)*3, v___x_2659_);
lean_ctor_set_float(v___x_2662_, sizeof(void*)*3 + 8, v___x_2659_);
lean_ctor_set_uint8(v___x_2662_, sizeof(void*)*3 + 16, v___x_2658_);
return v___x_2662_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4));
v___x_2667_ = l_Lean_MessageData_ofFormat(v___x_2666_);
return v___x_2667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8));
v___x_2673_ = l_Lean_stringToMessageData(v___x_2672_);
return v___x_2673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10));
v___x_2676_ = l_Lean_stringToMessageData(v___x_2675_);
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12));
v___x_2679_ = l_Lean_stringToMessageData(v___x_2678_);
return v___x_2679_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14));
v___x_2682_ = l_Lean_stringToMessageData(v___x_2681_);
return v___x_2682_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16));
v___x_2685_ = l_Lean_stringToMessageData(v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(lean_object* v_c_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_toGoalState_2691_; lean_object* v_exprs_2692_; lean_object* v_ematch_2693_; lean_object* v_split_2694_; lean_object* v___x_2695_; lean_object* v_msgs_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___x_2730_; lean_object* v_splits_2731_; lean_object* v_ematch_2732_; lean_object* v_gen_2733_; lean_object* v_instances_2734_; lean_object* v_numInstances_2735_; lean_object* v_num_2736_; lean_object* v___x_2737_; lean_object* v_msgs_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v_msgs_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v_msgs_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; uint8_t v___x_2796_; 
v_toGoalState_2691_ = lean_ctor_get(v_a_2687_, 0);
v_exprs_2692_ = lean_ctor_get(v_toGoalState_2691_, 2);
v_ematch_2693_ = lean_ctor_get(v_toGoalState_2691_, 12);
v_split_2694_ = lean_ctor_get(v_toGoalState_2691_, 14);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2730_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_2687_, v_exprs_2692_, v___x_2695_, v___x_2695_);
v_splits_2731_ = lean_ctor_get(v_c_2686_, 0);
v_ematch_2732_ = lean_ctor_get(v_c_2686_, 1);
v_gen_2733_ = lean_ctor_get(v_c_2686_, 2);
v_instances_2734_ = lean_ctor_get(v_c_2686_, 4);
v_numInstances_2735_ = lean_ctor_get(v_ematch_2693_, 4);
v_num_2736_ = lean_ctor_get(v_ematch_2693_, 6);
v___x_2737_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2796_ = lean_nat_dec_le(v_instances_2734_, v_numInstances_2735_);
if (v___x_2796_ == 0)
{
v_msgs_2778_ = v___x_2737_;
v___y_2779_ = v_a_2688_;
v___y_2780_ = v_a_2689_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; double v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2800_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2801_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2801_, 0, v___x_2797_);
lean_ctor_set(v___x_2801_, 1, v___x_2798_);
lean_ctor_set(v___x_2801_, 2, v___x_2800_);
lean_ctor_set_float(v___x_2801_, sizeof(void*)*3, v___x_2799_);
lean_ctor_set_float(v___x_2801_, sizeof(void*)*3 + 8, v___x_2799_);
lean_ctor_set_uint8(v___x_2801_, sizeof(void*)*3 + 16, v___x_2796_);
v___x_2802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17);
lean_inc(v_instances_2734_);
v___x_2803_ = l_Nat_reprFast(v_instances_2734_);
v___x_2804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
v___x_2805_ = l_Lean_MessageData_ofFormat(v___x_2804_);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2802_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2801_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
lean_ctor_set(v___x_2809_, 2, v___x_2737_);
v___x_2810_ = lean_array_push(v___x_2737_, v___x_2809_);
v_msgs_2778_ = v___x_2810_;
v___y_2779_ = v_a_2688_;
v___y_2780_ = v_a_2689_;
goto v___jp_2777_;
}
v___jp_2696_:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(v_a_2687_, v_c_2686_, v_msgs_2697_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2716_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2703_ = v___x_2700_;
v_isShared_2704_ = v_isSharedCheck_2716_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2700_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2716_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = lean_array_get_size(v_a_2701_);
v___x_2706_ = lean_nat_dec_eq(v___x_2705_, v___x_2695_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_del_object(v___x_2703_);
v___x_2707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2);
v___x_2708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5);
v___x_2709_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
lean_ctor_set(v___x_2709_, 2, v_a_2701_);
v___x_2710_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2709_, v___y_2698_);
return v___x_2710_;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_dec(v_a_2701_);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v___y_2698_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2712_);
v___x_2714_ = v___x_2703_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v___y_2698_);
v_a_2717_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2719_ = v___x_2700_;
v_isShared_2720_ = v_isSharedCheck_2729_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2700_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2729_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_ref_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v_ref_2721_ = lean_ctor_get(v___y_2699_, 5);
v___x_2722_ = lean_io_error_to_string(v_a_2717_);
v___x_2723_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
v___x_2724_ = l_Lean_MessageData_ofFormat(v___x_2723_);
lean_inc(v_ref_2721_);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v_ref_2721_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2725_);
v___x_2727_ = v___x_2719_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
v___jp_2738_:
{
uint8_t v___x_2742_; 
v___x_2742_ = lean_nat_dec_le(v_gen_2733_, v___x_2730_);
lean_dec(v___x_2730_);
if (v___x_2742_ == 0)
{
v_msgs_2697_ = v_msgs_2739_;
v___y_2698_ = v___y_2740_;
v___y_2699_ = v___y_2741_;
goto v___jp_2696_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; double v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2746_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2747_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2747_, 0, v___x_2743_);
lean_ctor_set(v___x_2747_, 1, v___x_2744_);
lean_ctor_set(v___x_2747_, 2, v___x_2746_);
lean_ctor_set_float(v___x_2747_, sizeof(void*)*3, v___x_2745_);
lean_ctor_set_float(v___x_2747_, sizeof(void*)*3 + 8, v___x_2745_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*3 + 16, v___x_2742_);
v___x_2748_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9);
lean_inc(v_gen_2733_);
v___x_2749_ = l_Nat_reprFast(v_gen_2733_);
v___x_2750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
v___x_2751_ = l_Lean_MessageData_ofFormat(v___x_2750_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2748_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2747_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
lean_ctor_set(v___x_2755_, 2, v___x_2737_);
v___x_2756_ = lean_array_push(v_msgs_2739_, v___x_2755_);
v_msgs_2697_ = v___x_2756_;
v___y_2698_ = v___y_2740_;
v___y_2699_ = v___y_2741_;
goto v___jp_2696_;
}
}
v___jp_2757_:
{
lean_object* v_num_2761_; uint8_t v___x_2762_; 
v_num_2761_ = lean_ctor_get(v_split_2694_, 0);
v___x_2762_ = lean_nat_dec_le(v_splits_2731_, v_num_2761_);
if (v___x_2762_ == 0)
{
v_msgs_2739_ = v_msgs_2758_;
v___y_2740_ = v___y_2759_;
v___y_2741_ = v___y_2760_;
goto v___jp_2738_;
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; double v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2764_ = lean_box(0);
v___x_2765_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2766_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2767_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2767_, 0, v___x_2763_);
lean_ctor_set(v___x_2767_, 1, v___x_2764_);
lean_ctor_set(v___x_2767_, 2, v___x_2766_);
lean_ctor_set_float(v___x_2767_, sizeof(void*)*3, v___x_2765_);
lean_ctor_set_float(v___x_2767_, sizeof(void*)*3 + 8, v___x_2765_);
lean_ctor_set_uint8(v___x_2767_, sizeof(void*)*3 + 16, v___x_2762_);
v___x_2768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13);
lean_inc(v_splits_2731_);
v___x_2769_ = l_Nat_reprFast(v_splits_2731_);
v___x_2770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
v___x_2771_ = l_Lean_MessageData_ofFormat(v___x_2770_);
v___x_2772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2768_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2767_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
lean_ctor_set(v___x_2775_, 2, v___x_2737_);
v___x_2776_ = lean_array_push(v_msgs_2758_, v___x_2775_);
v_msgs_2739_ = v___x_2776_;
v___y_2740_ = v___y_2759_;
v___y_2741_ = v___y_2760_;
goto v___jp_2738_;
}
}
v___jp_2777_:
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_nat_dec_le(v_ematch_2732_, v_num_2736_);
if (v___x_2781_ == 0)
{
v_msgs_2758_ = v_msgs_2778_;
v___y_2759_ = v___y_2779_;
v___y_2760_ = v___y_2780_;
goto v___jp_2757_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; double v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2783_ = lean_box(0);
v___x_2784_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2785_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2786_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2786_, 0, v___x_2782_);
lean_ctor_set(v___x_2786_, 1, v___x_2783_);
lean_ctor_set(v___x_2786_, 2, v___x_2785_);
lean_ctor_set_float(v___x_2786_, sizeof(void*)*3, v___x_2784_);
lean_ctor_set_float(v___x_2786_, sizeof(void*)*3 + 8, v___x_2784_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*3 + 16, v___x_2781_);
v___x_2787_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15);
lean_inc(v_ematch_2732_);
v___x_2788_ = l_Nat_reprFast(v_ematch_2732_);
v___x_2789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
v___x_2790_ = l_Lean_MessageData_ofFormat(v___x_2789_);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2787_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2786_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
lean_ctor_set(v___x_2794_, 2, v___x_2737_);
v___x_2795_ = lean_array_push(v_msgs_2778_, v___x_2794_);
v_msgs_2758_ = v___x_2795_;
v___y_2759_ = v___y_2779_;
v___y_2760_ = v___y_2780_;
goto v___jp_2757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___boxed(lean_object* v_c_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_c_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec_ref(v_a_2814_);
lean_dec_ref(v_a_2812_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(lean_object* v_c_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_c_2817_, v_a_2818_, v_a_2819_, v_a_2822_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___boxed(lean_object* v_c_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(v_c_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec_ref(v_a_2827_);
return v_res_2834_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2838_; uint8_t v___x_2839_; double v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2838_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2839_ = 1;
v___x_2840_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2841_ = lean_box(0);
v___x_2842_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1));
v___x_2843_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
lean_ctor_set(v___x_2843_, 1, v___x_2841_);
lean_ctor_set(v___x_2843_, 2, v___x_2838_);
lean_ctor_set_float(v___x_2843_, sizeof(void*)*3, v___x_2840_);
lean_ctor_set_float(v___x_2843_, sizeof(void*)*3 + 8, v___x_2840_);
lean_ctor_set_uint8(v___x_2843_, sizeof(void*)*3 + 16, v___x_2839_);
return v___x_2843_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3));
v___x_2846_ = l_Lean_stringToMessageData(v___x_2845_);
return v___x_2846_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2));
v___x_2848_ = l_Lean_stringToMessageData(v___x_2847_);
return v___x_2848_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6));
v___x_2851_ = l_Lean_stringToMessageData(v___x_2850_);
return v___x_2851_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8));
v___x_2854_ = l_Lean_stringToMessageData(v___x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(lean_object* v_as_x27_2855_, lean_object* v_b_2856_, lean_object* v___y_2857_){
_start:
{
if (lean_obj_tag(v_as_x27_2855_) == 0)
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v_b_2856_);
lean_ctor_set(v___x_2859_, 1, v___y_2857_);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
else
{
lean_object* v_head_2861_; lean_object* v_tail_2862_; lean_object* v_expr_2863_; lean_object* v_i_2864_; lean_object* v_num_2865_; lean_object* v_source_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_head_2861_ = lean_ctor_get(v_as_x27_2855_, 0);
v_tail_2862_ = lean_ctor_get(v_as_x27_2855_, 1);
v_expr_2863_ = lean_ctor_get(v_head_2861_, 0);
v_i_2864_ = lean_ctor_get(v_head_2861_, 1);
v_num_2865_ = lean_ctor_get(v_head_2861_, 2);
v_source_2866_ = lean_ctor_get(v_head_2861_, 3);
v___x_2867_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2868_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
v___x_2869_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4);
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = lean_nat_add(v_i_2864_, v___x_2870_);
v___x_2872_ = l_Nat_reprFast(v___x_2871_);
v___x_2873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
v___x_2874_ = l_Lean_MessageData_ofFormat(v___x_2873_);
v___x_2875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2869_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
lean_inc(v_num_2865_);
v___x_2878_ = l_Nat_reprFast(v_num_2865_);
v___x_2879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
v___x_2880_ = l_Lean_MessageData_ofFormat(v___x_2879_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2877_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7);
v___x_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
lean_inc_ref(v_expr_2863_);
v___x_2884_ = l_Lean_MessageData_ofExpr(v_expr_2863_);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9);
lean_inc(v_source_2866_);
v___x_2887_ = l_Lean_Meta_Grind_SplitSource_toMessageData(v_source_2866_);
v___x_2888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2868_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
lean_ctor_set(v___x_2889_, 2, v___x_2867_);
v___x_2890_ = lean_mk_empty_array_with_capacity(v___x_2870_);
v___x_2891_ = lean_array_push(v___x_2890_, v___x_2889_);
v___x_2892_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2868_);
lean_ctor_set(v___x_2892_, 1, v___x_2885_);
lean_ctor_set(v___x_2892_, 2, v___x_2891_);
v___x_2893_ = lean_array_push(v_b_2856_, v___x_2892_);
v_as_x27_2855_ = v_tail_2862_;
v_b_2856_ = v___x_2893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___boxed(lean_object* v_as_x27_2895_, lean_object* v_b_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_2895_, v_b_2896_, v___y_2897_);
lean_dec(v_as_x27_2895_);
return v_res_2899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1));
v___x_2904_ = l_Lean_MessageData_ofFormat(v___x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_toGoalState_2912_; lean_object* v_split_2913_; lean_object* v_trace_2914_; uint8_t v___x_2915_; 
v_toGoalState_2912_ = lean_ctor_get(v_a_2905_, 0);
v_split_2913_ = lean_ctor_get(v_toGoalState_2912_, 14);
v_trace_2914_ = lean_ctor_get(v_split_2913_, 4);
v___x_2915_ = l_List_isEmpty___redArg(v_trace_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v_a_2919_; lean_object* v_fst_2920_; lean_object* v_snd_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2916_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
lean_inc(v_trace_2914_);
v___x_2917_ = l_List_reverse___redArg(v_trace_2914_);
v___x_2918_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v___x_2917_, v___x_2916_, v_a_2906_);
lean_dec(v___x_2917_);
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref(v___x_2918_);
v_fst_2920_ = lean_ctor_get(v_a_2919_, 0);
lean_inc(v_fst_2920_);
v_snd_2921_ = lean_ctor_get(v_a_2919_, 1);
lean_inc(v_snd_2921_);
lean_dec(v_a_2919_);
v___x_2922_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
v___x_2923_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2);
v___x_2924_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
lean_ctor_set(v___x_2924_, 2, v_fst_2920_);
v___x_2925_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2924_, v_snd_2921_);
return v___x_2925_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = lean_box(0);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v_a_2906_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___boxed(lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec_ref(v_a_2929_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(lean_object* v_as_2937_, lean_object* v_as_x27_2938_, lean_object* v_b_2939_, lean_object* v_a_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_2938_, v_b_2939_, v___y_2942_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___boxed(lean_object* v_as_2949_, lean_object* v_as_x27_2950_, lean_object* v_b_2951_, lean_object* v_a_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(v_as_2949_, v_as_x27_2950_, v_b_2951_, v_a_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec_ref(v___y_2953_);
lean_dec(v_as_x27_2950_);
lean_dec(v_as_2949_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(lean_object* v_goal_2965_, lean_object* v_config_2966_, uint8_t v_collapsedMain_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_toGoalState_2975_; lean_object* v_facts_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v_a_2983_; lean_object* v_snd_2984_; lean_object* v___x_2985_; 
v_toGoalState_2975_ = lean_ctor_get(v_goal_2965_, 0);
v_facts_2976_ = lean_ctor_get(v_toGoalState_2975_, 10);
v___x_2977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1));
v___x_2978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2));
v___x_2979_ = l_Lean_PersistentArray_toArray___redArg(v_facts_2976_);
v___x_2980_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_2981_ = l_Lean_Meta_Grind_ppExprArray(v___x_2977_, v___x_2978_, v___x_2979_, v___x_2980_, v_collapsedMain_2967_);
v___x_2982_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2981_, v_a_2969_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
v_snd_2984_ = lean_ctor_get(v_a_2983_, 1);
lean_inc(v_snd_2984_);
lean_dec(v_a_2983_);
v___x_2985_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(v_collapsedMain_2967_, v_a_2968_, v_snd_2984_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v_snd_2987_; lean_object* v___x_2988_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v_snd_2987_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_snd_2987_);
lean_dec(v_a_2986_);
v___x_2988_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(v_a_2968_, v_snd_2987_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v_snd_2990_; lean_object* v___x_2991_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v_snd_2990_ = lean_ctor_get(v_a_2989_, 1);
lean_inc(v_snd_2990_);
lean_dec(v_a_2989_);
v___x_2991_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(v_a_2968_, v_snd_2990_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v_snd_2993_; lean_object* v___x_2994_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v_snd_2993_ = lean_ctor_get(v_a_2992_, 1);
lean_inc(v_snd_2993_);
lean_dec(v_a_2992_);
v___x_2994_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(v_a_2968_, v_snd_2993_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v_snd_2996_; lean_object* v___x_2997_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2994_, 1);
v_snd_2996_ = lean_ctor_get(v_a_2995_, 1);
lean_inc(v_snd_2996_);
lean_dec(v_a_2995_);
v___x_2997_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(v_a_2968_, v_snd_2996_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v_snd_2999_; lean_object* v___x_3000_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v_snd_2999_ = lean_ctor_get(v_a_2998_, 1);
lean_inc(v_snd_2999_);
lean_dec(v_a_2998_);
v___x_3000_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(v_a_2968_, v_snd_2999_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v_snd_3002_; lean_object* v___x_3003_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v_snd_3002_ = lean_ctor_get(v_a_3001_, 1);
lean_inc(v_snd_3002_);
lean_dec(v_a_3001_);
v___x_3003_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(v_a_2968_, v_snd_3002_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v_snd_3005_; lean_object* v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v_snd_3005_ = lean_ctor_get(v_a_3004_, 1);
lean_inc(v_snd_3005_);
lean_dec(v_a_3004_);
v___x_3006_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_config_2966_, v_a_2968_, v_snd_3005_, v_a_2972_);
return v___x_3006_;
}
else
{
lean_dec_ref(v_config_2966_);
return v___x_3003_;
}
}
else
{
lean_dec_ref(v_config_2966_);
return v___x_3000_;
}
}
else
{
lean_dec_ref(v_config_2966_);
return v___x_2997_;
}
}
else
{
lean_dec_ref(v_config_2966_);
return v___x_2994_;
}
}
else
{
lean_dec_ref(v_config_2966_);
return v___x_2991_;
}
}
else
{
lean_dec_ref(v_config_2966_);
return v___x_2988_;
}
}
else
{
lean_dec_ref(v_config_2966_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___boxed(lean_object* v_goal_3007_, lean_object* v_config_3008_, lean_object* v_collapsedMain_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
uint8_t v_collapsedMain_boxed_3017_; lean_object* v_res_3018_; 
v_collapsedMain_boxed_3017_ = lean_unbox(v_collapsedMain_3009_);
v_res_3018_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_3007_, v_config_3008_, v_collapsedMain_boxed_3017_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec_ref(v_a_3010_);
lean_dec_ref(v_goal_3007_);
return v_res_3018_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2(void){
_start:
{
lean_object* v___x_3022_; uint8_t v___x_3023_; double v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3022_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_3023_ = 0;
v___x_3024_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_3025_ = lean_box(0);
v___x_3026_ = ((lean_object*)(l_Lean_Meta_Grind_goalDiagToMessageData___closed__1));
v___x_3027_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v___x_3025_);
lean_ctor_set(v___x_3027_, 2, v___x_3022_);
lean_ctor_set_float(v___x_3027_, sizeof(void*)*3, v___x_3024_);
lean_ctor_set_float(v___x_3027_, sizeof(void*)*3 + 8, v___x_3024_);
lean_ctor_set_uint8(v___x_3027_, sizeof(void*)*3 + 16, v___x_3023_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData(lean_object* v_goal_3028_, lean_object* v_config_3029_, lean_object* v_header_3030_, uint8_t v_collapsedMain_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_3038_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_3028_, v_config_3029_, v_collapsedMain_3031_, v_goal_3028_, v___x_3037_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3051_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3051_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3051_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v_snd_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v_snd_3043_ = lean_ctor_get(v_a_3039_, 1);
lean_inc(v_snd_3043_);
lean_dec(v_a_3039_);
v___x_3044_ = lean_obj_once(&l_Lean_Meta_Grind_goalDiagToMessageData___closed__2, &l_Lean_Meta_Grind_goalDiagToMessageData___closed__2_once, _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2);
v___x_3045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3045_, 0, v_header_3030_);
v___x_3046_ = l_Lean_MessageData_ofFormat(v___x_3045_);
v___x_3047_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3044_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
lean_ctor_set(v___x_3047_, 2, v_snd_3043_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3047_);
v___x_3049_ = v___x_3041_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v_header_3030_);
v_a_3052_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3038_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3038_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___boxed(lean_object* v_goal_3060_, lean_object* v_config_3061_, lean_object* v_header_3062_, lean_object* v_collapsedMain_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
uint8_t v_collapsedMain_boxed_3069_; lean_object* v_res_3070_; 
v_collapsedMain_boxed_3069_ = lean_unbox(v_collapsedMain_3063_);
v_res_3070_ = l_Lean_Meta_Grind_goalDiagToMessageData(v_goal_3060_, v_config_3061_, v_header_3062_, v_collapsedMain_boxed_3069_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec_ref(v_goal_3060_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(lean_object* v_msgData_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; lean_object* v_env_3078_; lean_object* v___x_3079_; lean_object* v_mctx_3080_; lean_object* v_lctx_3081_; lean_object* v_options_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3077_ = lean_st_ref_get(v___y_3075_);
v_env_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_env_3078_);
lean_dec(v___x_3077_);
v___x_3079_ = lean_st_ref_get(v___y_3073_);
v_mctx_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc_ref(v_mctx_3080_);
lean_dec(v___x_3079_);
v_lctx_3081_ = lean_ctor_get(v___y_3072_, 2);
v_options_3082_ = lean_ctor_get(v___y_3074_, 2);
lean_inc_ref(v_options_3082_);
lean_inc_ref(v_lctx_3081_);
v___x_3083_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3083_, 0, v_env_3078_);
lean_ctor_set(v___x_3083_, 1, v_mctx_3080_);
lean_ctor_set(v___x_3083_, 2, v_lctx_3081_);
lean_ctor_set(v___x_3083_, 3, v_options_3082_);
v___x_3084_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set(v___x_3084_, 1, v_msgData_3071_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0___boxed(lean_object* v_msgData_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(v_msgData_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(lean_object* v_mvarId_3093_, lean_object* v_x_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3093_, v_x_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3100_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3100_);
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
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg___boxed(lean_object* v_mvarId_3117_, lean_object* v_x_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3117_, v_x_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(lean_object* v_00_u03b1_3125_, lean_object* v_mvarId_3126_, lean_object* v_x_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3126_, v_x_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___boxed(lean_object* v_00_u03b1_3134_, lean_object* v_mvarId_3135_, lean_object* v_x_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(v_00_u03b1_3134_, v_mvarId_3135_, v_x_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
return v_res_3142_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0));
v___x_3145_ = l_Lean_stringToMessageData(v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0(uint8_t v_verbose_3146_, lean_object* v_mvarId_3147_, lean_object* v_goal_3148_, lean_object* v_config_3149_, uint8_t v___x_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
if (v_verbose_3146_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec_ref(v_config_3149_);
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v_mvarId_3147_);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = ((lean_object*)(l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0));
v___x_3159_ = l_Lean_Meta_Grind_goalDiagToMessageData(v_goal_3148_, v_config_3149_, v___x_3158_, v___x_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3171_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3171_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3171_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 1);
lean_ctor_set(v___x_3162_, 0, v_mvarId_3147_);
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_mvarId_3147_);
v___x_3165_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3166_ = lean_obj_once(&l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1, &l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v_a_3160_);
v___x_3169_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(v___x_3168_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3169_;
}
}
}
else
{
lean_dec(v_mvarId_3147_);
return v___x_3159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed(lean_object* v_verbose_3172_, lean_object* v_mvarId_3173_, lean_object* v_goal_3174_, lean_object* v_config_3175_, lean_object* v___x_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
uint8_t v_verbose_boxed_3182_; uint8_t v___x_1179__boxed_3183_; lean_object* v_res_3184_; 
v_verbose_boxed_3182_ = lean_unbox(v_verbose_3172_);
v___x_1179__boxed_3183_ = lean_unbox(v___x_3176_);
v_res_3184_ = l_Lean_Meta_Grind_goalToMessageData___lam__0(v_verbose_boxed_3182_, v_mvarId_3173_, v_goal_3174_, v_config_3175_, v___x_1179__boxed_3183_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v_goal_3174_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object* v_goal_3185_, lean_object* v_config_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
uint8_t v_verbose_3192_; lean_object* v_mvarId_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___y_3197_; lean_object* v___x_3198_; 
v_verbose_3192_ = lean_ctor_get_uint8(v_config_3186_, sizeof(void*)*13 + 15);
v_mvarId_3193_ = lean_ctor_get(v_goal_3185_, 1);
lean_inc_n(v_mvarId_3193_, 2);
v___x_3194_ = 1;
v___x_3195_ = lean_box(v_verbose_3192_);
v___x_3196_ = lean_box(v___x_3194_);
v___y_3197_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed), 10, 5);
lean_closure_set(v___y_3197_, 0, v___x_3195_);
lean_closure_set(v___y_3197_, 1, v_mvarId_3193_);
lean_closure_set(v___y_3197_, 2, v_goal_3185_);
lean_closure_set(v___y_3197_, 3, v_config_3186_);
lean_closure_set(v___y_3197_, 4, v___x_3196_);
v___x_3198_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3193_, v___y_3197_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___boxed(lean_object* v_goal_3199_, lean_object* v_config_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_Meta_Grind_goalToMessageData(v_goal_3199_, v_config_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
return v_res_3206_;
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
