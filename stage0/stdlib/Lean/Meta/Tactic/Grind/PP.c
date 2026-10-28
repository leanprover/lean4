// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PP
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Sym.Arith.Types import Init.Grind.Util import Init.Grind.Injective import Init.Grind.PP import Lean.Meta.Tactic.Grind.Arith.CommRing.PP import Lean.Meta.Tactic.Grind.Arith.Linear.PP import Lean.Meta.Tactic.Grind.AC.PP import Lean.Meta.Tactic.Grind.CastLike import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_SplitSource_toMessageData(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_AC_pp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", [ctor]"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", [val]"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__7_value)}};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__4_value),LEAN_SCALAR_PTR_LITERAL(179, 194, 82, 68, 109, 146, 236, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 97, .m_data = "maximum number of steps performed by the `lia` solver has been reached, threshold: `(liaSteps := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "maximum term generation has been reached, threshold: `(gen := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "maximum number of case-splits has been reached, threshold: `(splits := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "maximum number of E-matching rounds has been reached, threshold: `(ematch := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "maximum number of instances generated by E-matching has been reached, threshold: `(instances := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__19;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_goalDiagToMessageData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_goalDiagToMessageData___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_goalDiagToMessageData___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_goalDiagToMessageData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_197_; uint8_t v___x_217_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_217_ = l_Lean_Expr_isApp(v_e_190_);
if (v___x_217_ == 0)
{
lean_dec(v_a_197_);
goto v___jp_198_;
}
else
{
uint8_t v___x_218_; 
v___x_218_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
if (v___x_218_ == 0)
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
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec_ref(v_e_190_);
v_a_225_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_196_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_196_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue___boxed(lean_object* v_goal_233_, lean_object* v_e_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(v_goal_233_, v_e_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_goal_233_);
return v_res_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(lean_object* v_opts_241_, lean_object* v_opt_242_){
_start:
{
lean_object* v_name_243_; lean_object* v_defValue_244_; lean_object* v_map_245_; lean_object* v___x_246_; 
v_name_243_ = lean_ctor_get(v_opt_242_, 0);
v_defValue_244_ = lean_ctor_get(v_opt_242_, 1);
v_map_245_ = lean_ctor_get(v_opts_241_, 0);
v___x_246_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_245_, v_name_243_);
if (lean_obj_tag(v___x_246_) == 0)
{
uint8_t v___x_247_; 
v___x_247_ = lean_unbox(v_defValue_244_);
return v___x_247_;
}
else
{
lean_object* v_val_248_; 
v_val_248_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v___x_246_, 1);
if (lean_obj_tag(v_val_248_) == 1)
{
uint8_t v_v_249_; 
v_v_249_ = lean_ctor_get_uint8(v_val_248_, 0);
lean_dec_ref_known(v_val_248_, 0);
return v_v_249_;
}
else
{
uint8_t v___x_250_; 
lean_dec(v_val_248_);
v___x_250_ = lean_unbox(v_defValue_244_);
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0___boxed(lean_object* v_opts_251_, lean_object* v_opt_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(v_opts_251_, v_opt_252_);
lean_dec_ref(v_opt_252_);
lean_dec_ref(v_opts_251_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__0));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__2));
v___x_260_ = l_Lean_stringToMessageData(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__5));
v___x_265_ = l_Lean_MessageData_ofFormat(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__8));
v___x_270_ = l_Lean_MessageData_ofFormat(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__11(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__10));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(lean_object* v_goal_274_, lean_object* v_e_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_r_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___x_306_; 
lean_inc_ref(v_e_275_);
v___x_306_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_274_, v_e_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
lean_inc_ref(v_e_275_);
v___x_308_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDeclValue(v_goal_274_, v_e_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_308_, 1);
v___x_310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3);
v___x_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_311_, 0, v_a_307_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_a_309_);
lean_inc_ref(v_e_275_);
v___x_313_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_274_, v_e_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v_root_315_; uint8_t v_interpreted_316_; uint8_t v_ctor_317_; lean_object* v_r_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v_r_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; size_t v___x_334_; size_t v___x_335_; uint8_t v___x_336_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_313_, 1);
v_root_315_ = lean_ctor_get(v_a_314_, 2);
lean_inc_ref(v_root_315_);
v_interpreted_316_ = lean_ctor_get_uint8(v_a_314_, sizeof(void*)*12 + 1);
v_ctor_317_ = lean_ctor_get_uint8(v_a_314_, sizeof(void*)*12 + 2);
lean_dec(v_a_314_);
v___x_334_ = lean_ptr_addr(v_e_275_);
v___x_335_ = lean_ptr_addr(v_root_315_);
v___x_336_ = lean_usize_dec_eq(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_274_, v_root_315_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
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
lean_ctor_set(v___x_341_, 0, v___x_312_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v_r_327_ = v___x_341_;
v___y_328_ = v_a_276_;
v___y_329_ = v_a_277_;
v___y_330_ = v_a_278_;
v___y_331_ = v_a_279_;
goto v___jp_326_;
}
else
{
lean_dec_ref_known(v___x_312_, 2);
lean_dec_ref(v_e_275_);
return v___x_337_;
}
}
else
{
lean_dec_ref(v_root_315_);
v_r_327_ = v___x_312_;
v___y_328_ = v_a_276_;
v___y_329_ = v_a_277_;
v___y_330_ = v_a_278_;
v___y_331_ = v_a_279_;
goto v___jp_326_;
}
v___jp_318_:
{
if (v_ctor_317_ == 0)
{
v_r_282_ = v_r_319_;
v___y_283_ = v___y_320_;
v___y_284_ = v___y_321_;
v___y_285_ = v___y_322_;
v___y_286_ = v___y_323_;
goto v___jp_281_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__6);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v_r_319_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v_r_282_ = v___x_325_;
v___y_283_ = v___y_320_;
v___y_284_ = v___y_321_;
v___y_285_ = v___y_322_;
v___y_286_ = v___y_323_;
goto v___jp_281_;
}
}
v___jp_326_:
{
if (v_interpreted_316_ == 0)
{
v_r_319_ = v_r_327_;
v___y_320_ = v___y_328_;
v___y_321_ = v___y_329_;
v___y_322_ = v___y_330_;
v___y_323_ = v___y_331_;
goto v___jp_318_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__9);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v_r_327_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v_r_319_ = v___x_333_;
v___y_320_ = v___y_328_;
v___y_321_ = v___y_329_;
v___y_322_ = v___y_330_;
v___y_323_ = v___y_331_;
goto v___jp_318_;
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref_known(v___x_312_, 2);
lean_dec_ref(v_e_275_);
v_a_342_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_313_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_313_);
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
lean_dec(v_a_307_);
lean_dec_ref(v_e_275_);
return v___x_308_;
}
}
else
{
lean_dec_ref(v_e_275_);
return v___x_306_;
}
v___jp_281_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_287_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_285_);
v___x_288_ = l_Lean_Meta_Grind_grind_debug;
v___x_289_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl_spec__0(v___x_287_, v___x_288_);
lean_dec_ref(v___x_287_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec_ref(v_e_275_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_r_282_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v_goal_274_, v_e_275_);
lean_dec_ref(v_e_275_);
if (lean_obj_tag(v___x_291_) == 1)
{
lean_object* v_val_292_; lean_object* v___x_293_; 
v_val_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v___x_291_, 1);
v___x_293_ = l_Lean_Meta_Grind_Goal_ppENodeRef(v_goal_274_, v_val_292_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_304_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_304_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__1);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_a_294_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v_r_282_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_300_);
v___x_302_ = v___x_296_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_dec_ref(v_r_282_);
return v___x_293_;
}
}
else
{
lean_object* v___x_305_; 
lean_dec(v___x_291_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v_r_282_);
return v___x_305_;
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
lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_480_; 
v___x_478_ = lean_box(0);
v_a_479_ = lean_array_uget_borrowed(v_as_463_, v_i_465_);
lean_inc(v_a_479_);
v___x_480_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_462_, v_a_479_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v_self_482_; lean_object* v___x_483_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
v_self_482_ = lean_ctor_get(v_a_481_, 0);
lean_inc_ref(v_self_482_);
lean_dec(v_a_481_);
v___x_483_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_462_, v_self_482_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v___x_485_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v_snd_474_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_a_484_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_487_);
lean_ctor_set(v___x_476_, 0, v___x_478_);
v___x_489_ = v___x_476_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_478_);
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
v_a_494_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_483_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_483_);
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
v_a_502_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_480_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_480_);
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
lean_object* v___x_541_; lean_object* v_a_542_; lean_object* v___x_543_; 
v___x_541_ = lean_box(0);
v_a_542_ = lean_array_uget_borrowed(v_as_526_, v_i_528_);
lean_inc(v_a_542_);
v___x_543_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_525_, v_a_542_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v_self_545_; lean_object* v___x_546_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v_self_545_ = lean_ctor_get(v_a_544_, 0);
lean_inc_ref(v_self_545_);
lean_dec(v_a_544_);
v___x_546_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_525_, v_self_545_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v_snd_537_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_a_547_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_550_);
lean_ctor_set(v___x_539_, 0, v___x_541_);
v___x_552_ = v___x_539_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_541_);
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
v_a_557_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_546_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_546_);
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
v_a_565_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_543_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_543_);
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
lean_object* v___x_672_; lean_object* v_a_673_; lean_object* v___x_674_; 
v___x_672_ = lean_box(0);
v_a_673_ = lean_array_uget_borrowed(v_as_657_, v_i_659_);
lean_inc(v_snd_668_);
v___x_674_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Goal_ppState_spec__1_spec__1(v_init_655_, v_goal_656_, v_a_673_, v_snd_668_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_693_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_693_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_693_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_693_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
if (lean_obj_tag(v_a_675_) == 0)
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v_a_675_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_679_);
v___x_681_ = v___x_670_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_snd_668_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_683_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_681_);
v___x_683_ = v___x_677_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; 
lean_del_object(v___x_677_);
lean_dec(v_snd_668_);
v_a_686_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v_a_675_, 1);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_a_686_);
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_688_ = v___x_670_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_a_686_);
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
v_a_694_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_674_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_674_);
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
lean_object* v___x_744_; lean_object* v_a_745_; lean_object* v___x_746_; 
v___x_744_ = lean_box(0);
v_a_745_ = lean_array_uget_borrowed(v_as_729_, v_i_731_);
lean_inc(v_a_745_);
v___x_746_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_728_, v_a_745_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v_self_748_; lean_object* v___x_749_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v_self_748_ = lean_ctor_get(v_a_747_, 0);
lean_inc_ref(v_self_748_);
lean_dec(v_a_747_);
v___x_749_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_728_, v_self_748_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v_snd_740_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_a_750_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___x_753_);
lean_ctor_set(v___x_742_, 0, v___x_744_);
v___x_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_744_);
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
v_a_760_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_749_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_749_);
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
v_a_768_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_746_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_746_);
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
lean_object* v___x_807_; lean_object* v_a_808_; lean_object* v___x_809_; 
v___x_807_ = lean_box(0);
v_a_808_ = lean_array_uget_borrowed(v_as_792_, v_i_794_);
lean_inc(v_a_808_);
v___x_809_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_791_, v_a_808_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v_self_811_; lean_object* v___x_812_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v_self_811_ = lean_ctor_get(v_a_810_, 0);
lean_inc_ref(v_self_811_);
lean_dec(v_a_810_);
v___x_812_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl(v_goal_791_, v_self_811_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__2);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v_snd_803_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v_a_813_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_816_);
lean_ctor_set(v___x_805_, 0, v___x_807_);
v___x_818_ = v___x_805_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_807_);
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
v_a_823_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_812_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_812_);
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
v_a_831_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_809_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_809_);
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
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__1));
v___x_1143_ = lean_name_eq(v_declName_1141_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__3));
v___x_1145_ = lean_name_eq(v_declName_1141_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___closed__5));
v___x_1147_ = lean_name_eq(v_declName_1141_, v___x_1146_);
return v___x_1147_;
}
else
{
return v___x_1145_;
}
}
else
{
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin___boxed(lean_object* v_declName_1148_){
_start:
{
uint8_t v_res_1149_; lean_object* v_r_1150_; 
v_res_1149_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_1148_);
lean_dec(v_declName_1148_);
v_r_1150_ = lean_box(v_res_1149_);
return v_r_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___impl(uint8_t v_x_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_box(v_x_1151_);
v___x_1153_ = lean_obj_tag_nat(v___x_1152_);
lean_dec(v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___impl___boxed(lean_object* v_x_1154_){
_start:
{
uint8_t v_x_4__boxed_1155_; lean_object* v_res_1156_; 
v_x_4__boxed_1155_ = lean_unbox(v_x_1154_);
v_res_1156_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorIdx___impl(v_x_4__boxed_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(lean_object* v_k_1157_){
_start:
{
lean_inc(v_k_1157_);
return v_k_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg___boxed(lean_object* v_k_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___redArg(v_k_1158_);
lean_dec(v_k_1158_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(lean_object* v_motive_1160_, lean_object* v_ctorIdx_1161_, uint8_t v_t_1162_, lean_object* v_h_1163_, lean_object* v_k_1164_){
_start:
{
lean_inc(v_k_1164_);
return v_k_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim___boxed(lean_object* v_motive_1165_, lean_object* v_ctorIdx_1166_, lean_object* v_t_1167_, lean_object* v_h_1168_, lean_object* v_k_1169_){
_start:
{
uint8_t v_t_boxed_1170_; lean_object* v_res_1171_; 
v_t_boxed_1170_ = lean_unbox(v_t_1167_);
v_res_1171_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_ctorElim(v_motive_1165_, v_ctorIdx_1166_, v_t_boxed_1170_, v_h_1168_, v_k_1169_);
lean_dec(v_k_1169_);
lean_dec(v_ctorIdx_1166_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(lean_object* v_num_1172_){
_start:
{
lean_inc(v_num_1172_);
return v_num_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg___boxed(lean_object* v_num_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___redArg(v_num_1173_);
lean_dec(v_num_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(lean_object* v_motive_1175_, uint8_t v_t_1176_, lean_object* v_h_1177_, lean_object* v_num_1178_){
_start:
{
lean_inc(v_num_1178_);
return v_num_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim___boxed(lean_object* v_motive_1179_, lean_object* v_t_1180_, lean_object* v_h_1181_, lean_object* v_num_1182_){
_start:
{
uint8_t v_t_boxed_1183_; lean_object* v_res_1184_; 
v_t_boxed_1183_ = lean_unbox(v_t_1180_);
v_res_1184_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_num_elim(v_motive_1179_, v_t_boxed_1183_, v_h_1181_, v_num_1182_);
lean_dec(v_num_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(lean_object* v_cast_1185_){
_start:
{
lean_inc(v_cast_1185_);
return v_cast_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg___boxed(lean_object* v_cast_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___redArg(v_cast_1186_);
lean_dec(v_cast_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(lean_object* v_motive_1188_, uint8_t v_t_1189_, lean_object* v_h_1190_, lean_object* v_cast_1191_){
_start:
{
lean_inc(v_cast_1191_);
return v_cast_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim___boxed(lean_object* v_motive_1192_, lean_object* v_t_1193_, lean_object* v_h_1194_, lean_object* v_cast_1195_){
_start:
{
uint8_t v_t_boxed_1196_; lean_object* v_res_1197_; 
v_t_boxed_1196_ = lean_unbox(v_t_1193_);
v_res_1197_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_cast_elim(v_motive_1192_, v_t_boxed_1196_, v_h_1194_, v_cast_1195_);
lean_dec(v_cast_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(lean_object* v_no_1198_){
_start:
{
lean_inc(v_no_1198_);
return v_no_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg___boxed(lean_object* v_no_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___redArg(v_no_1199_);
lean_dec(v_no_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(lean_object* v_motive_1201_, uint8_t v_t_1202_, lean_object* v_h_1203_, lean_object* v_no_1204_){
_start:
{
lean_inc(v_no_1204_);
return v_no_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim___boxed(lean_object* v_motive_1205_, lean_object* v_t_1206_, lean_object* v_h_1207_, lean_object* v_no_1208_){
_start:
{
uint8_t v_t_boxed_1209_; lean_object* v_res_1210_; 
v_t_boxed_1209_ = lean_unbox(v_t_1206_);
v_res_1210_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Result_no_elim(v_motive_1205_, v_t_boxed_1209_, v_h_1207_, v_no_1208_);
lean_dec(v_no_1208_);
return v_res_1210_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedResult_default(void){
_start:
{
uint8_t v___x_1211_; 
v___x_1211_ = 0;
return v___x_1211_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_instInhabitedResult(void){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = 0;
return v___x_1212_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(lean_object* v_e_1253_){
_start:
{
lean_object* v_a_1259_; lean_object* v_b_1260_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = l_Lean_Expr_cleanupAnnotations(v_e_1253_);
v___x_1265_ = l_Lean_Expr_isApp(v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec_ref(v___x_1264_);
goto v___jp_1254_;
}
else
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1264_);
v___x_1267_ = l_Lean_Expr_isApp(v___x_1266_);
if (v___x_1267_ == 0)
{
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1264_);
goto v___jp_1254_;
}
else
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1266_);
v___x_1269_ = l_Lean_Expr_isApp(v___x_1268_);
if (v___x_1269_ == 0)
{
lean_dec_ref(v___x_1268_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1264_);
goto v___jp_1254_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1268_);
lean_dec_ref(v___x_1268_);
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__2));
v___x_1272_ = l_Lean_Expr_isConstOf(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v_arg_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_arg_1273_ = lean_ctor_get(v___x_1264_, 1);
lean_inc_ref(v_arg_1273_);
lean_dec_ref(v___x_1264_);
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__5));
v___x_1275_ = l_Lean_Expr_isConstOf(v___x_1270_, v___x_1274_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; 
v___x_1276_ = l_Lean_Expr_isApp(v___x_1270_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v_arg_1273_);
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1266_);
goto v___jp_1254_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1270_);
lean_dec_ref(v___x_1270_);
v___x_1278_ = l_Lean_Expr_isApp(v___x_1277_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_arg_1273_);
lean_dec_ref(v___x_1266_);
goto v___jp_1254_;
}
else
{
lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1277_);
lean_dec_ref(v___x_1277_);
v___x_1280_ = l_Lean_Expr_isApp(v___x_1279_);
if (v___x_1280_ == 0)
{
lean_dec_ref(v___x_1279_);
lean_dec_ref(v_arg_1273_);
lean_dec_ref(v___x_1266_);
goto v___jp_1254_;
}
else
{
lean_object* v_arg_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_arg_1281_ = lean_ctor_get(v___x_1266_, 1);
lean_inc_ref(v_arg_1281_);
lean_dec_ref(v___x_1266_);
v___x_1282_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__8));
v___x_1284_ = l_Lean_Expr_isConstOf(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__11));
v___x_1286_ = l_Lean_Expr_isConstOf(v___x_1282_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__14));
v___x_1288_ = l_Lean_Expr_isConstOf(v___x_1282_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__17));
v___x_1290_ = l_Lean_Expr_isConstOf(v___x_1282_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__20));
v___x_1292_ = l_Lean_Expr_isConstOf(v___x_1282_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___closed__23));
v___x_1294_ = l_Lean_Expr_isConstOf(v___x_1282_, v___x_1293_);
lean_dec_ref(v___x_1282_);
if (v___x_1294_ == 0)
{
lean_dec_ref(v_arg_1281_);
lean_dec_ref(v_arg_1273_);
goto v___jp_1254_;
}
else
{
lean_dec_ref(v_e_1253_);
v_a_1259_ = v_arg_1281_;
v_b_1260_ = v_arg_1273_;
goto v___jp_1258_;
}
}
else
{
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_e_1253_);
v_a_1259_ = v_arg_1281_;
v_b_1260_ = v_arg_1273_;
goto v___jp_1258_;
}
}
else
{
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_e_1253_);
v_a_1259_ = v_arg_1281_;
v_b_1260_ = v_arg_1273_;
goto v___jp_1258_;
}
}
else
{
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_e_1253_);
v_a_1259_ = v_arg_1281_;
v_b_1260_ = v_arg_1273_;
goto v___jp_1258_;
}
}
else
{
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_e_1253_);
v_a_1259_ = v_arg_1281_;
v_b_1260_ = v_arg_1273_;
goto v___jp_1258_;
}
}
else
{
lean_dec_ref(v___x_1282_);
lean_dec_ref(v_arg_1273_);
lean_dec_ref(v_e_1253_);
v_e_1253_ = v_arg_1281_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v_e_1253_);
v_e_1253_ = v_arg_1273_;
goto _start;
}
}
else
{
uint8_t v___x_1297_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___x_1264_);
lean_dec_ref(v_e_1253_);
v___x_1297_ = 0;
return v___x_1297_;
}
}
}
}
v___jp_1254_:
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_Meta_Grind_isCastLikeApp(v_e_1253_);
lean_dec_ref(v_e_1253_);
if (v___x_1255_ == 0)
{
uint8_t v___x_1256_; 
v___x_1256_ = 2;
return v___x_1256_;
}
else
{
uint8_t v___x_1257_; 
v___x_1257_ = 1;
return v___x_1257_;
}
}
v___jp_1258_:
{
uint8_t v___x_1261_; 
v___x_1261_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_a_1259_);
switch(v___x_1261_)
{
case 0:
{
v_e_1253_ = v_b_1260_;
goto _start;
}
case 1:
{
uint8_t v___x_1263_; 
v___x_1263_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_b_1260_);
switch(v___x_1263_)
{
case 2:
{
return v___x_1263_;
}
case 1:
{
return v___x_1263_;
}
default: 
{
return v___x_1261_;
}
}
}
default: 
{
lean_dec_ref(v_b_1260_);
return v___x_1261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go___boxed(lean_object* v_e_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_1298_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(lean_object* v_e_1301_){
_start:
{
uint8_t v___x_1302_; 
v___x_1302_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike_go(v_e_1301_);
if (v___x_1302_ == 1)
{
uint8_t v___x_1303_; 
v___x_1303_ = 1;
return v___x_1303_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = 0;
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike___boxed(lean_object* v_e_1305_){
_start:
{
uint8_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_1305_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(lean_object* v_declName_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v_env_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_st_ref_get(v___y_1309_);
v_env_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc_ref(v_env_1312_);
lean_dec(v___x_1311_);
v___x_1313_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1312_, v_declName_1308_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg___boxed(lean_object* v_declName_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1315_, v___y_1316_);
lean_dec(v___y_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(lean_object* v_declName_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1319_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___boxed(lean_object* v_declName_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0(v_declName_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp(lean_object* v_e_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
uint8_t v___x_1339_; uint8_t v___x_1340_; 
lean_inc_ref(v_e_1333_);
v___x_1339_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isArithOfCastLike(v_e_1333_);
v___x_1340_ = 1;
if (v___x_1339_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_Expr_getAppFn(v_e_1333_);
if (lean_obj_tag(v___x_1341_) == 4)
{
lean_object* v_declName_1342_; lean_object* v___y_1344_; lean_object* v___x_1359_; lean_object* v_a_1360_; 
v_declName_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc_n(v_declName_1342_, 2);
lean_dec_ref_known(v___x_1341_, 2);
v___x_1359_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_isSupportApp_spec__0___redArg(v_declName_1342_, v_a_1337_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
if (lean_obj_tag(v_a_1360_) == 1)
{
lean_object* v_val_1361_; lean_object* v_numParams_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_val_1361_ = lean_ctor_get(v_a_1360_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v_a_1360_, 1);
v_numParams_1362_ = lean_ctor_get(v_val_1361_, 1);
lean_inc(v_numParams_1362_);
lean_dec(v_val_1361_);
v___x_1363_ = l_Lean_Expr_getAppNumArgs(v_e_1333_);
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = lean_nat_add(v_numParams_1362_, v___x_1364_);
lean_dec(v_numParams_1362_);
v___x_1366_ = lean_nat_dec_eq(v___x_1363_, v___x_1365_);
lean_dec(v___x_1365_);
lean_dec(v___x_1363_);
if (v___x_1366_ == 0)
{
lean_dec_ref(v_e_1333_);
v___y_1344_ = v_a_1337_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = l_Lean_Expr_appArg_x21(v_e_1333_);
lean_dec_ref(v_e_1333_);
v___x_1368_ = l_Lean_Meta_isConstructorApp(v___x_1367_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1378_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_unbox(v_a_1369_);
lean_dec(v_a_1369_);
if (v___x_1373_ == 0)
{
lean_del_object(v___x_1371_);
v___y_1344_ = v_a_1337_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec(v_declName_1342_);
v___x_1374_ = lean_box(v___x_1340_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1374_);
v___x_1376_ = v___x_1371_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_dec(v_declName_1342_);
return v___x_1368_;
}
}
}
else
{
lean_dec(v_a_1360_);
lean_dec_ref(v_e_1333_);
v___y_1344_ = v_a_1337_;
goto v___jp_1343_;
}
v___jp_1343_:
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = lean_st_ref_get(v___y_1344_);
v___x_1346_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_1342_);
if (v___x_1346_ == 0)
{
uint8_t v___x_1347_; 
v___x_1347_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isGadget(v_declName_1342_);
if (v___x_1347_ == 0)
{
uint8_t v___x_1348_; 
v___x_1348_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_isBuiltin(v_declName_1342_);
if (v___x_1348_ == 0)
{
lean_object* v_env_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_env_1349_ = lean_ctor_get(v___x_1345_, 0);
lean_inc_ref(v_env_1349_);
lean_dec(v___x_1345_);
v___x_1350_ = l_Lean_Meta_isMatcherCore(v_env_1349_, v_declName_1342_);
v___x_1351_ = lean_box(v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec(v___x_1345_);
lean_dec(v_declName_1342_);
v___x_1353_ = lean_box(v___x_1340_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v___x_1345_);
lean_dec(v_declName_1342_);
v___x_1355_ = lean_box(v___x_1340_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v___x_1345_);
lean_dec(v_declName_1342_);
v___x_1357_ = lean_box(v___x_1340_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref(v___x_1341_);
lean_dec_ref(v_e_1333_);
v___x_1379_ = lean_box(v___x_1339_);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec_ref(v_e_1333_);
v___x_1381_ = lean_box(v___x_1340_);
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSupportApp___boxed(lean_object* v_e_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Meta_Grind_isSupportApp(v_e_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
if (lean_obj_tag(v_a_1390_) == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = l_List_reverse___redArg(v_a_1391_);
return v___x_1392_;
}
else
{
lean_object* v_head_1393_; lean_object* v_tail_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1403_; 
v_head_1393_ = lean_ctor_get(v_a_1390_, 0);
v_tail_1394_ = lean_ctor_get(v_a_1390_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_a_1390_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1396_ = v_a_1390_;
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_tail_1394_);
lean_inc(v_head_1393_);
lean_dec(v_a_1390_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = l_Lean_MessageData_ofExpr(v_head_1393_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 1, v_a_1391_);
lean_ctor_set(v___x_1396_, 0, v___x_1398_);
v___x_1400_ = v___x_1396_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_a_1391_);
v___x_1400_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
v_a_1390_ = v_tail_1394_;
v_a_1391_ = v___x_1400_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__2(void){
_start:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; double v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1407_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1408_ = 1;
v___x_1409_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1410_ = lean_box(0);
v___x_1411_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1412_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v___x_1410_);
lean_ctor_set(v___x_1412_, 2, v___x_1407_);
lean_ctor_set_float(v___x_1412_, sizeof(void*)*3, v___x_1409_);
lean_ctor_set_float(v___x_1412_, sizeof(void*)*3 + 8, v___x_1409_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*3 + 16, v___x_1408_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__5(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__4));
v___x_1417_ = l_Lean_MessageData_ofFormat(v___x_1416_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_ppEqc___closed__6(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_ppGoals_spec__0___redArg___closed__0);
v___x_1419_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__5, &l_Lean_Meta_Grind_ppEqc___closed__5_once, _init_l_Lean_Meta_Grind_ppEqc___closed__5);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v___x_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppEqc(lean_object* v_eqc_1421_, lean_object* v_children_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1423_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__2, &l_Lean_Meta_Grind_ppEqc___closed__2_once, _init_l_Lean_Meta_Grind_ppEqc___closed__2);
v___x_1424_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__5);
v___x_1425_ = lean_box(0);
v___x_1426_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_ppEqc_spec__0(v_eqc_1421_, v___x_1425_);
v___x_1427_ = lean_obj_once(&l_Lean_Meta_Grind_ppEqc___closed__6, &l_Lean_Meta_Grind_ppEqc___closed__6_once, _init_l_Lean_Meta_Grind_ppEqc___closed__6);
v___x_1428_ = l_Lean_MessageData_joinSep(v___x_1426_, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1424_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__11);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1423_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
lean_ctor_set(v___x_1433_, 2, v_children_1422_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
if (lean_obj_tag(v_a_1434_) == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = l_List_reverse___redArg(v_a_1435_);
return v___x_1436_;
}
else
{
lean_object* v_head_1437_; lean_object* v_tail_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1448_; 
v_head_1437_ = lean_ctor_get(v_a_1434_, 0);
v_tail_1438_ = lean_ctor_get(v_a_1434_, 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_a_1434_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1440_ = v_a_1434_;
v_isShared_1441_ = v_isSharedCheck_1448_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_tail_1438_);
lean_inc(v_head_1437_);
lean_dec(v_a_1434_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1448_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
uint8_t v___x_1442_; 
v___x_1442_ = l_Lean_Expr_isTrue(v_head_1437_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1444_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 1, v_a_1435_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_head_1437_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_a_1435_);
v___x_1444_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
v_a_1434_ = v_tail_1438_;
v_a_1435_ = v___x_1444_;
goto _start;
}
}
else
{
lean_del_object(v___x_1440_);
lean_dec(v_head_1437_);
v_a_1434_ = v_tail_1438_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
if (lean_obj_tag(v_a_1449_) == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = l_List_reverse___redArg(v_a_1450_);
return v___x_1451_;
}
else
{
lean_object* v_head_1452_; lean_object* v_tail_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1463_; 
v_head_1452_ = lean_ctor_get(v_a_1449_, 0);
v_tail_1453_ = lean_ctor_get(v_a_1449_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_a_1449_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1455_ = v_a_1449_;
v_isShared_1456_ = v_isSharedCheck_1463_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_tail_1453_);
lean_inc(v_head_1452_);
lean_dec(v_a_1449_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1463_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
uint8_t v___x_1457_; 
v___x_1457_ = l_Lean_Expr_isFalse(v_head_1452_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1459_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v_a_1450_);
v___x_1459_ = v___x_1455_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_head_1452_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1450_);
v___x_1459_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
v_a_1449_ = v_tail_1453_;
v_a_1450_ = v___x_1459_;
goto _start;
}
}
else
{
lean_del_object(v___x_1455_);
lean_dec(v_head_1452_);
v_a_1449_ = v_tail_1453_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___redArg(uint8_t v_a_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
if (lean_obj_tag(v_x_1465_) == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_x_1466_);
lean_ctor_set(v___x_1473_, 1, v___y_1467_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
else
{
lean_object* v_head_1475_; lean_object* v_tail_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1498_; 
v_head_1475_ = lean_ctor_get(v_x_1465_, 0);
v_tail_1476_ = lean_ctor_get(v_x_1465_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_x_1465_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1478_ = v_x_1465_;
v_isShared_1479_ = v_isSharedCheck_1498_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_tail_1476_);
lean_inc(v_head_1475_);
lean_dec(v_x_1465_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1498_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_snd_1481_; lean_object* v___x_1486_; 
lean_inc(v_head_1475_);
v___x_1486_ = l_Lean_Meta_Grind_isSupportApp(v_head_1475_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; uint8_t v___x_1488_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1488_ = lean_unbox(v_a_1487_);
lean_dec(v_a_1487_);
if (v___x_1488_ == 0)
{
v_snd_1481_ = v___y_1467_;
goto v___jp_1480_;
}
else
{
if (v_a_1464_ == 0)
{
lean_del_object(v___x_1478_);
lean_dec(v_head_1475_);
v_x_1465_ = v_tail_1476_;
goto _start;
}
else
{
v_snd_1481_ = v___y_1467_;
goto v___jp_1480_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_del_object(v___x_1478_);
lean_dec(v_tail_1476_);
lean_dec(v_head_1475_);
lean_dec_ref(v___y_1467_);
lean_dec(v_x_1466_);
v_a_1490_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1486_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1486_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
v___jp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 1, v_x_1466_);
v___x_1483_ = v___x_1478_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_head_1475_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_x_1466_);
v___x_1483_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
v_x_1465_ = v_tail_1476_;
v_x_1466_ = v___x_1483_;
v___y_1467_ = v_snd_1481_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___redArg___boxed(lean_object* v_a_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v_a_17475__boxed_1508_; lean_object* v_res_1509_; 
v_a_17475__boxed_1508_ = lean_unbox(v_a_1499_);
v_res_1509_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___redArg(v_a_17475__boxed_1508_, v_x_1500_, v_x_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(lean_object* v_x_1510_){
_start:
{
if (lean_obj_tag(v_x_1510_) == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_box(0);
return v___x_1511_;
}
else
{
lean_object* v_head_1512_; lean_object* v_tail_1513_; uint8_t v___x_1514_; 
v_head_1512_ = lean_ctor_get(v_x_1510_, 0);
v_tail_1513_ = lean_ctor_get(v_x_1510_, 1);
v___x_1514_ = l_Lean_Expr_isFalse(v_head_1512_);
if (v___x_1514_ == 0)
{
v_x_1510_ = v_tail_1513_;
goto _start;
}
else
{
lean_object* v___x_1516_; 
lean_inc(v_head_1512_);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_head_1512_);
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1___boxed(lean_object* v_x_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(v_x_1517_);
lean_dec(v_x_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(lean_object* v_x_1519_){
_start:
{
if (lean_obj_tag(v_x_1519_) == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_box(0);
return v___x_1520_;
}
else
{
lean_object* v_head_1521_; lean_object* v_tail_1522_; uint8_t v___x_1523_; 
v_head_1521_ = lean_ctor_get(v_x_1519_, 0);
v_tail_1522_ = lean_ctor_get(v_x_1519_, 1);
v___x_1523_ = l_Lean_Expr_isTrue(v_head_1521_);
if (v___x_1523_ == 0)
{
v_x_1519_ = v_tail_1522_;
goto _start;
}
else
{
lean_object* v___x_1525_; 
lean_inc(v_head_1521_);
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_head_1521_);
return v___x_1525_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0___boxed(lean_object* v_x_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(v_x_1526_);
lean_dec(v_x_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
if (lean_obj_tag(v_x_1528_) == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_x_1529_);
lean_ctor_set(v___x_1536_, 1, v___y_1530_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
else
{
lean_object* v_head_1538_; lean_object* v_tail_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1559_; 
v_head_1538_ = lean_ctor_get(v_x_1528_, 0);
v_tail_1539_ = lean_ctor_get(v_x_1528_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_x_1528_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1541_ = v_x_1528_;
v_isShared_1542_ = v_isSharedCheck_1559_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_tail_1539_);
lean_inc(v_head_1538_);
lean_dec(v_x_1528_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1559_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; 
lean_inc(v_head_1538_);
v___x_1543_ = l_Lean_Meta_Grind_isSupportApp(v_head_1538_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; uint8_t v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = lean_unbox(v_a_1544_);
lean_dec(v_a_1544_);
if (v___x_1545_ == 0)
{
lean_del_object(v___x_1541_);
lean_dec(v_head_1538_);
v_x_1528_ = v_tail_1539_;
goto _start;
}
else
{
lean_object* v___x_1548_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 1, v_x_1529_);
v___x_1548_ = v___x_1541_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_head_1538_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_x_1529_);
v___x_1548_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
v_x_1528_ = v_tail_1539_;
v_x_1529_ = v___x_1548_;
goto _start;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_del_object(v___x_1541_);
lean_dec(v_tail_1539_);
lean_dec(v_head_1538_);
lean_dec_ref(v___y_1530_);
lean_dec(v_x_1529_);
v_a_1551_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1543_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1543_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg___boxed(lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_x_1560_, v_x_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(uint8_t v_collapsedProps_1574_, lean_object* v_as_x27_1575_, lean_object* v_b_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
if (lean_obj_tag(v_as_x27_1575_) == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v_b_1576_);
lean_ctor_set(v___x_1584_, 1, v___y_1578_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
else
{
lean_object* v_snd_1586_; lean_object* v_snd_1587_; lean_object* v_head_1588_; lean_object* v_tail_1589_; lean_object* v_fst_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1757_; 
v_snd_1586_ = lean_ctor_get(v_b_1576_, 1);
lean_inc(v_snd_1586_);
v_snd_1587_ = lean_ctor_get(v_snd_1586_, 1);
lean_inc(v_snd_1587_);
v_head_1588_ = lean_ctor_get(v_as_x27_1575_, 0);
v_tail_1589_ = lean_ctor_get(v_as_x27_1575_, 1);
v_fst_1590_ = lean_ctor_get(v_b_1576_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_b_1576_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; 
v_unused_1758_ = lean_ctor_get(v_b_1576_, 1);
lean_dec(v_unused_1758_);
v___x_1592_ = v_b_1576_;
v_isShared_1593_ = v_isSharedCheck_1757_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_fst_1590_);
lean_dec(v_b_1576_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1757_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_fst_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1755_; 
v_fst_1594_ = lean_ctor_get(v_snd_1586_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_snd_1586_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_snd_1586_, 1);
lean_dec(v_unused_1756_);
v___x_1596_ = v_snd_1586_;
v_isShared_1597_ = v_isSharedCheck_1755_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_fst_1594_);
lean_dec(v_snd_1586_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1755_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1754_; 
v_fst_1598_ = lean_ctor_get(v_snd_1587_, 0);
v_snd_1599_ = lean_ctor_get(v_snd_1587_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_snd_1587_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1601_ = v_snd_1587_;
v_isShared_1602_ = v_isSharedCheck_1754_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_snd_1599_);
lean_inc(v_fst_1598_);
lean_dec(v_snd_1587_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1754_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___y_1604_; lean_object* v___x_1615_; 
v___x_1615_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__0(v_head_1588_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = l_List_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__1(v_head_1588_);
if (lean_obj_tag(v___x_1616_) == 0)
{
if (lean_obj_tag(v_head_1588_) == 1)
{
lean_object* v_tail_1617_; 
v_tail_1617_ = lean_ctor_get(v_head_1588_, 1);
if (lean_obj_tag(v_tail_1617_) == 1)
{
lean_object* v_head_1618_; lean_object* v_regularEqcs_1619_; lean_object* v___x_1620_; 
lean_del_object(v___x_1601_);
lean_del_object(v___x_1596_);
lean_del_object(v___x_1592_);
v_head_1618_ = lean_ctor_get(v_head_1588_, 0);
v_regularEqcs_1619_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
lean_inc(v_head_1618_);
v___x_1620_ = l_Lean_Meta_isProof(v_head_1618_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; uint8_t v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = lean_unbox(v_a_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_unbox(v_a_1621_);
lean_dec(v_a_1621_);
lean_inc_ref(v_head_1588_);
v___x_1625_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___redArg(v___x_1624_, v_head_1588_, v___x_1623_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1685_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v_fst_1627_ = lean_ctor_get(v_a_1626_, 0);
v_snd_1628_ = lean_ctor_get(v_a_1626_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_a_1626_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1630_ = v_a_1626_;
v_isShared_1631_ = v_isSharedCheck_1685_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_snd_1628_);
lean_inc(v_fst_1627_);
lean_dec(v_a_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1685_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1632_ = l_List_reverse___redArg(v_fst_1627_);
v___x_1633_ = l_List_lengthTR___redArg(v___x_1632_);
v___x_1634_ = lean_unsigned_to_nat(1u);
v___x_1635_ = lean_nat_dec_le(v___x_1633_, v___x_1634_);
lean_dec(v___x_1633_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
lean_inc_ref(v_head_1588_);
v___x_1636_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_head_1588_, v___x_1623_, v_snd_1628_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v_fst_1638_; lean_object* v_snd_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1668_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v_fst_1638_ = lean_ctor_get(v_a_1637_, 0);
v_snd_1639_ = lean_ctor_get(v_a_1637_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_a_1637_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1641_ = v_a_1637_;
v_isShared_1642_ = v_isSharedCheck_1668_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_snd_1639_);
lean_inc(v_fst_1638_);
lean_dec(v_a_1637_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1668_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = l_List_reverse___redArg(v_fst_1638_);
v___x_1644_ = l_List_isEmpty___redArg(v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1645_ = l_Lean_Meta_Grind_ppEqc(v___x_1643_, v_regularEqcs_1619_);
v___x_1646_ = lean_mk_empty_array_with_capacity(v___x_1634_);
v___x_1647_ = lean_array_push(v___x_1646_, v___x_1645_);
v___x_1648_ = l_Lean_Meta_Grind_ppEqc(v___x_1632_, v___x_1647_);
v___x_1649_ = lean_array_push(v_fst_1598_, v___x_1648_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 1, v_snd_1599_);
lean_ctor_set(v___x_1641_, 0, v___x_1649_);
v___x_1651_ = v___x_1641_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_snd_1599_);
v___x_1651_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___x_1651_);
lean_ctor_set(v___x_1630_, 0, v_fst_1594_);
v___x_1653_ = v___x_1630_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_fst_1594_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_fst_1590_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1654_;
v___y_1578_ = v_snd_1639_;
goto _start;
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_dec(v___x_1643_);
v___x_1658_ = l_Lean_Meta_Grind_ppEqc(v___x_1632_, v_regularEqcs_1619_);
v___x_1659_ = lean_array_push(v_fst_1598_, v___x_1658_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 1, v_snd_1599_);
lean_ctor_set(v___x_1641_, 0, v___x_1659_);
v___x_1661_ = v___x_1641_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_snd_1599_);
v___x_1661_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___x_1661_);
lean_ctor_set(v___x_1630_, 0, v_fst_1594_);
v___x_1663_ = v___x_1630_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_fst_1594_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_fst_1590_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1664_;
v___y_1578_ = v_snd_1639_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v___x_1632_);
lean_del_object(v___x_1630_);
lean_dec(v_snd_1599_);
lean_dec(v_fst_1598_);
lean_dec(v_fst_1594_);
lean_dec(v_fst_1590_);
v_a_1669_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1636_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1636_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_dec(v___x_1632_);
lean_inc_ref(v_head_1588_);
v___x_1677_ = l_Lean_Meta_Grind_ppEqc(v_head_1588_, v_regularEqcs_1619_);
v___x_1678_ = lean_array_push(v_snd_1599_, v___x_1677_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___x_1678_);
lean_ctor_set(v___x_1630_, 0, v_fst_1598_);
v___x_1680_ = v___x_1630_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_fst_1598_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_fst_1594_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_fst_1590_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1682_;
v___y_1578_ = v_snd_1628_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_snd_1599_);
lean_dec(v_fst_1598_);
lean_dec(v_fst_1594_);
lean_dec(v_fst_1590_);
v_a_1686_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1625_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1625_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v_a_1621_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_fst_1598_);
lean_ctor_set(v___x_1694_, 1, v_snd_1599_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_fst_1594_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_fst_1590_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1696_;
goto _start;
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_snd_1599_);
lean_dec(v_fst_1598_);
lean_dec(v_fst_1594_);
lean_dec(v_fst_1590_);
lean_dec_ref(v___y_1578_);
v_a_1698_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1620_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1620_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
v___y_1604_ = v___y_1578_;
goto v___jp_1603_;
}
}
else
{
v___y_1604_ = v___y_1578_;
goto v___jp_1603_;
}
}
else
{
lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1728_; 
lean_del_object(v___x_1601_);
lean_del_object(v___x_1596_);
lean_del_object(v___x_1592_);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v___x_1616_, 0);
lean_dec(v_unused_1729_);
v___x_1707_ = v___x_1616_;
v_isShared_1708_ = v_isSharedCheck_1728_;
goto v_resetjp_1706_;
}
else
{
lean_dec(v___x_1616_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1728_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1709_ = lean_box(0);
lean_inc(v_head_1588_);
v___x_1710_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__4(v_head_1588_, v___x_1709_);
v___x_1711_ = l_List_isEmpty___redArg(v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_dec(v_fst_1594_);
v___x_1712_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1713_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__0));
v___x_1714_ = lean_array_mk(v___x_1710_);
v___x_1715_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_1716_ = l_Lean_Meta_Grind_ppExprArray(v___x_1712_, v___x_1713_, v___x_1714_, v___x_1715_, v_collapsedProps_1574_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1716_);
v___x_1718_ = v___x_1707_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_fst_1598_);
lean_ctor_set(v___x_1719_, 1, v_snd_1599_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_fst_1590_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1721_;
goto _start;
}
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_dec(v___x_1710_);
lean_del_object(v___x_1707_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_fst_1598_);
lean_ctor_set(v___x_1724_, 1, v_snd_1599_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_fst_1594_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_fst_1590_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1726_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1752_; 
lean_del_object(v___x_1601_);
lean_del_object(v___x_1596_);
lean_del_object(v___x_1592_);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1615_, 0);
lean_dec(v_unused_1753_);
v___x_1731_ = v___x_1615_;
v_isShared_1732_ = v_isSharedCheck_1752_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v___x_1615_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1752_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1733_ = lean_box(0);
lean_inc(v_head_1588_);
v___x_1734_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__5(v_head_1588_, v___x_1733_);
v___x_1735_ = l_List_isEmpty___redArg(v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
lean_dec(v_fst_1590_);
v___x_1736_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1737_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__3));
v___x_1738_ = lean_array_mk(v___x_1734_);
v___x_1739_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_1740_ = l_Lean_Meta_Grind_ppExprArray(v___x_1736_, v___x_1737_, v___x_1738_, v___x_1739_, v_collapsedProps_1574_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1740_);
v___x_1742_ = v___x_1731_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_fst_1598_);
lean_ctor_set(v___x_1743_, 1, v_snd_1599_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v_fst_1594_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1742_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1745_;
goto _start;
}
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v___x_1734_);
lean_del_object(v___x_1731_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_fst_1598_);
lean_ctor_set(v___x_1748_, 1, v_snd_1599_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_fst_1594_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_fst_1590_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1750_;
goto _start;
}
}
}
v___jp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1602_ == 0)
{
v___x_1606_ = v___x_1601_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_fst_1598_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_snd_1599_);
v___x_1606_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v___x_1606_);
v___x_1608_ = v___x_1596_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_fst_1594_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1610_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 1, v___x_1608_);
v___x_1610_ = v___x_1592_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_fst_1590_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
v_as_x27_1575_ = v_tail_1589_;
v_b_1576_ = v___x_1610_;
v___y_1578_ = v___y_1604_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___boxed(lean_object* v_collapsedProps_1759_, lean_object* v_as_x27_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v_collapsedProps_boxed_1769_; lean_object* v_res_1770_; 
v_collapsedProps_boxed_1769_ = lean_unbox(v_collapsedProps_1759_);
v_res_1770_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_boxed_1769_, v_as_x27_1760_, v_b_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v___y_1762_);
lean_dec(v_as_x27_1760_);
return v_res_1770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0(void){
_start:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; double v___x_1773_; lean_object* v_trueEqc_x3f_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1771_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1772_ = 1;
v___x_1773_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v_trueEqc_x3f_1774_ = lean_box(0);
v___x_1775_ = ((lean_object*)(l_Lean_Meta_Grind_ppEqc___closed__1));
v___x_1776_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v_trueEqc_x3f_1774_);
lean_ctor_set(v___x_1776_, 2, v___x_1771_);
lean_ctor_set_float(v___x_1776_, sizeof(void*)*3, v___x_1773_);
lean_ctor_set_float(v___x_1776_, sizeof(void*)*3 + 8, v___x_1773_);
lean_ctor_set_uint8(v___x_1776_, sizeof(void*)*3 + 16, v___x_1772_);
return v___x_1776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__2));
v___x_1781_ = l_Lean_MessageData_ofFormat(v___x_1780_);
return v___x_1781_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__8));
v___x_1794_ = l_Lean_MessageData_ofFormat(v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(uint8_t v_collapsedProps_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1803_; uint8_t v___x_1804_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = 1;
v___x_1817_ = l_Lean_Meta_Grind_Goal_getEqcs(v_a_1796_, v___x_1804_);
v___x_1818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__6));
v___x_1819_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_1795_, v___x_1817_, v___x_1818_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v___x_1817_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v_fst_1821_; lean_object* v_snd_1822_; lean_object* v_snd_1823_; lean_object* v_fst_1824_; lean_object* v_fst_1825_; lean_object* v_snd_1826_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v_regularEqcs_1835_; lean_object* v___y_1836_; lean_object* v_fst_1841_; lean_object* v_snd_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v_fst_1821_ = lean_ctor_get(v_a_1820_, 0);
lean_inc(v_fst_1821_);
v_snd_1822_ = lean_ctor_get(v_fst_1821_, 1);
lean_inc(v_snd_1822_);
v_snd_1823_ = lean_ctor_get(v_a_1820_, 1);
lean_inc(v_snd_1823_);
lean_dec(v_a_1820_);
v_fst_1824_ = lean_ctor_get(v_fst_1821_, 0);
lean_inc(v_fst_1824_);
lean_dec(v_fst_1821_);
v_fst_1825_ = lean_ctor_get(v_snd_1822_, 0);
lean_inc(v_fst_1825_);
v_snd_1826_ = lean_ctor_get(v_snd_1822_, 1);
lean_inc(v_snd_1826_);
lean_dec(v_snd_1822_);
v_fst_1841_ = lean_ctor_get(v_snd_1826_, 0);
lean_inc(v_fst_1841_);
v_snd_1842_ = lean_ctor_get(v_snd_1826_, 1);
lean_inc(v_snd_1842_);
lean_dec(v_snd_1826_);
v___x_1843_ = lean_array_get_size(v_snd_1842_);
v___x_1844_ = lean_nat_dec_eq(v___x_1843_, v___x_1803_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
v___x_1846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__9);
v___x_1847_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
lean_ctor_set(v___x_1847_, 2, v_snd_1842_);
v___x_1848_ = lean_array_push(v_fst_1841_, v___x_1847_);
v_regularEqcs_1835_ = v___x_1848_;
v___y_1836_ = v_snd_1823_;
goto v___jp_1834_;
}
else
{
lean_dec(v_snd_1842_);
v_regularEqcs_1835_ = v_fst_1841_;
v___y_1836_ = v_snd_1823_;
goto v___jp_1834_;
}
v___jp_1827_:
{
if (lean_obj_tag(v_fst_1825_) == 1)
{
lean_object* v_val_1830_; lean_object* v___x_1831_; lean_object* v_a_1832_; lean_object* v_snd_1833_; 
v_val_1830_ = lean_ctor_get(v_fst_1825_, 0);
lean_inc(v_val_1830_);
lean_dec_ref_known(v_fst_1825_, 1);
v___x_1831_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_1830_, v___y_1829_);
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
v_snd_1833_ = lean_ctor_get(v_a_1832_, 1);
lean_inc(v_snd_1833_);
lean_dec(v_a_1832_);
v___y_1806_ = v___y_1828_;
v___y_1807_ = v_snd_1833_;
goto v___jp_1805_;
}
else
{
lean_dec(v_fst_1825_);
v___y_1806_ = v___y_1828_;
v___y_1807_ = v___y_1829_;
goto v___jp_1805_;
}
}
v___jp_1834_:
{
if (lean_obj_tag(v_fst_1824_) == 1)
{
lean_object* v_val_1837_; lean_object* v___x_1838_; lean_object* v_a_1839_; lean_object* v_snd_1840_; 
v_val_1837_ = lean_ctor_get(v_fst_1824_, 0);
lean_inc(v_val_1837_);
lean_dec_ref_known(v_fst_1824_, 1);
v___x_1838_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_1837_, v___y_1836_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref(v___x_1838_);
v_snd_1840_ = lean_ctor_get(v_a_1839_, 1);
lean_inc(v_snd_1840_);
lean_dec(v_a_1839_);
v___y_1828_ = v_regularEqcs_1835_;
v___y_1829_ = v_snd_1840_;
goto v___jp_1827_;
}
else
{
lean_dec(v_fst_1824_);
v___y_1828_ = v_regularEqcs_1835_;
v___y_1829_ = v___y_1836_;
goto v___jp_1827_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1819_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1819_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
v___jp_1805_:
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = lean_array_get_size(v___y_1806_);
v___x_1809_ = lean_nat_dec_eq(v___x_1808_, v___x_1803_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__0);
v___x_1811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___closed__3);
v___x_1812_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
lean_ctor_set(v___x_1812_, 2, v___y_1806_);
v___x_1813_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_1812_, v___y_1807_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_dec_ref(v___y_1806_);
v___x_1814_ = lean_box(0);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___y_1807_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs___boxed(lean_object* v_collapsedProps_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
uint8_t v_collapsedProps_boxed_1865_; lean_object* v_res_1866_; 
v_collapsedProps_boxed_1865_ = lean_unbox(v_collapsedProps_1857_);
v_res_1866_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(v_collapsedProps_boxed_1865_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec_ref(v_a_1858_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(uint8_t v_a_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___redArg(v_a_1867_, v_x_1868_, v_x_1869_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2___boxed(lean_object* v_a_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
uint8_t v_a_18227__boxed_1888_; lean_object* v_res_1889_; 
v_a_18227__boxed_1888_ = lean_unbox(v_a_1878_);
v_res_1889_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__2(v_a_18227__boxed_1888_, v_x_1879_, v_x_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1881_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___redArg(v_x_1890_, v_x_1891_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3___boxed(lean_object* v_x_1900_, lean_object* v_x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__3(v_x_1900_, v_x_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1902_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(uint8_t v_collapsedProps_1910_, lean_object* v_as_1911_, lean_object* v_as_x27_1912_, lean_object* v_b_1913_, lean_object* v_a_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg(v_collapsedProps_1910_, v_as_x27_1912_, v_b_1913_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___boxed(lean_object* v_collapsedProps_1923_, lean_object* v_as_1924_, lean_object* v_as_x27_1925_, lean_object* v_b_1926_, lean_object* v_a_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v_collapsedProps_boxed_1935_; lean_object* v_res_1936_; 
v_collapsedProps_boxed_1935_ = lean_unbox(v_collapsedProps_1923_);
v_res_1936_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6(v_collapsedProps_boxed_1935_, v_as_1924_, v_as_x27_1925_, v_b_1926_, v_a_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v___y_1928_);
lean_dec(v_as_x27_1925_);
lean_dec(v_as_1924_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
if (lean_obj_tag(v_a_1937_) == 0)
{
lean_object* v___x_1939_; 
v___x_1939_ = l_List_reverse___redArg(v_a_1938_);
return v___x_1939_;
}
else
{
lean_object* v_head_1940_; lean_object* v_tail_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1950_; 
v_head_1940_ = lean_ctor_get(v_a_1937_, 0);
v_tail_1941_ = lean_ctor_get(v_a_1937_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_a_1937_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1943_ = v_a_1937_;
v_isShared_1944_ = v_isSharedCheck_1950_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_tail_1941_);
lean_inc(v_head_1940_);
lean_dec(v_a_1937_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1950_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = l_Lean_Meta_Grind_ppPattern(v_head_1940_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 1, v_a_1938_);
lean_ctor_set(v___x_1943_, 0, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_a_1938_);
v___x_1947_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v_a_1937_ = v_tail_1941_;
v_a_1938_ = v___x_1947_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
if (lean_obj_tag(v_a_1951_) == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = l_List_reverse___redArg(v_a_1952_);
return v___x_1953_;
}
else
{
lean_object* v_head_1954_; lean_object* v_tail_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1963_; 
v_head_1954_ = lean_ctor_get(v_a_1951_, 0);
v_tail_1955_ = lean_ctor_get(v_a_1951_, 1);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_a_1951_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1957_ = v_a_1951_;
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_tail_1955_);
lean_inc(v_head_1954_);
lean_dec(v_a_1951_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_a_1952_);
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_head_1954_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_a_1952_);
v___x_1960_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
v_a_1951_ = v_tail_1955_;
v_a_1952_ = v___x_1960_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__0));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4(void){
_start:
{
lean_object* v___x_1970_; uint8_t v___x_1971_; double v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1970_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_1971_ = 1;
v___x_1972_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_1973_ = lean_box(0);
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__3));
v___x_1975_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v___x_1973_);
lean_ctor_set(v___x_1975_, 2, v___x_1970_);
lean_ctor_set_float(v___x_1975_, sizeof(void*)*3, v___x_1972_);
lean_ctor_set_float(v___x_1975_, sizeof(void*)*3 + 8, v___x_1972_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*3 + 16, v___x_1971_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(lean_object* v_thm_1976_){
_start:
{
lean_object* v_patterns_1978_; lean_object* v_origin_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v_m_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_patterns_1978_ = lean_ctor_get(v_thm_1976_, 3);
lean_inc(v_patterns_1978_);
v_origin_1979_ = lean_ctor_get(v_thm_1976_, 5);
lean_inc_ref(v_origin_1979_);
lean_dec_ref(v_thm_1976_);
v___x_1980_ = l_Lean_Meta_Grind_Origin_pp(v_origin_1979_);
v___x_1981_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__1);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_box(0);
v___x_1984_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__0(v_patterns_1978_, v___x_1983_);
v___x_1985_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem_spec__1(v___x_1984_, v___x_1983_);
v___x_1986_ = l_Lean_MessageData_ofList(v___x_1985_);
v_m_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_1987_, 0, v___x_1982_);
lean_ctor_set(v_m_1987_, 1, v___x_1986_);
v___x_1988_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___closed__4);
v___x_1989_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_1990_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v_m_1987_);
lean_ctor_set(v___x_1990_, 2, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg___boxed(lean_object* v_thm_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_thm_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(lean_object* v_thm_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_thm_1995_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___boxed(lean_object* v_thm_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem(v_thm_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(size_t v_sz_2009_, size_t v_i_2010_, lean_object* v_bs_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_lt(v_i_2010_, v_sz_2009_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_bs_2011_);
lean_ctor_set(v___x_2015_, 1, v___y_2012_);
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
return v___x_2016_;
}
else
{
lean_object* v_v_2017_; lean_object* v___x_2018_; lean_object* v_bs_x27_2019_; lean_object* v___x_2020_; 
v_v_2017_ = lean_array_uget(v_bs_2011_, v_i_2010_);
v___x_2018_ = lean_unsigned_to_nat(0u);
v_bs_x27_2019_ = lean_array_uset(v_bs_2011_, v_i_2010_, v___x_2018_);
v___x_2020_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEMatchTheorem___redArg(v_v_2017_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; size_t v___x_2022_; size_t v___x_2023_; lean_object* v___x_2024_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_2010_, v___x_2022_);
v___x_2024_ = lean_array_uset(v_bs_x27_2019_, v_i_2010_, v_a_2021_);
v_i_2010_ = v___x_2023_;
v_bs_2011_ = v___x_2024_;
goto _start;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v_bs_x27_2019_);
lean_dec_ref(v___y_2012_);
v_a_2026_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2020_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2020_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg___boxed(lean_object* v_sz_2034_, lean_object* v_i_2035_, lean_object* v_bs_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
size_t v_sz_boxed_2039_; size_t v_i_boxed_2040_; lean_object* v_res_2041_; 
v_sz_boxed_2039_ = lean_unbox_usize(v_sz_2034_);
lean_dec(v_sz_2034_);
v_i_boxed_2040_ = lean_unbox_usize(v_i_2035_);
lean_dec(v_i_2035_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_boxed_2039_, v_i_boxed_2040_, v_bs_2036_, v___y_2037_);
return v_res_2041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2(void){
_start:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; double v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2045_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2046_ = 1;
v___x_2047_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2048_ = lean_box(0);
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__1));
v___x_2050_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v___x_2048_);
lean_ctor_set(v___x_2050_, 2, v___x_2045_);
lean_ctor_set_float(v___x_2050_, sizeof(void*)*3, v___x_2047_);
lean_ctor_set_float(v___x_2050_, sizeof(void*)*3 + 8, v___x_2047_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*3 + 16, v___x_2046_);
return v___x_2050_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__4));
v___x_2055_ = l_Lean_MessageData_ofFormat(v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_toGoalState_2063_; lean_object* v_ematch_2064_; lean_object* v_thms_2065_; lean_object* v_newThms_2066_; lean_object* v___x_2067_; size_t v_sz_2068_; size_t v___x_2069_; lean_object* v___x_2070_; 
v_toGoalState_2063_ = lean_ctor_get(v_a_2056_, 0);
v_ematch_2064_ = lean_ctor_get(v_toGoalState_2063_, 13);
v_thms_2065_ = lean_ctor_get(v_ematch_2064_, 2);
v_newThms_2066_ = lean_ctor_get(v_ematch_2064_, 3);
v___x_2067_ = l_Lean_PersistentArray_toArray___redArg(v_thms_2065_);
v_sz_2068_ = lean_array_size(v___x_2067_);
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2068_, v___x_2069_, v___x_2067_, v_a_2057_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___x_2074_; size_t v_sz_2075_; lean_object* v___x_2076_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v_fst_2072_ = lean_ctor_get(v_a_2071_, 0);
lean_inc(v_fst_2072_);
v_snd_2073_ = lean_ctor_get(v_a_2071_, 1);
lean_inc(v_snd_2073_);
lean_dec(v_a_2071_);
v___x_2074_ = l_Lean_PersistentArray_toArray___redArg(v_newThms_2066_);
v_sz_2075_ = lean_array_size(v___x_2074_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2075_, v___x_2069_, v___x_2074_, v_snd_2073_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2102_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2102_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2102_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v_fst_2081_; lean_object* v_snd_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2101_; 
v_fst_2081_ = lean_ctor_get(v_a_2077_, 0);
v_snd_2082_ = lean_ctor_get(v_a_2077_, 1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_a_2077_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2084_ = v_a_2077_;
v_isShared_2085_ = v_isSharedCheck_2101_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_snd_2082_);
lean_inc(v_fst_2081_);
lean_dec(v_a_2077_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2101_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2086_ = l_Array_append___redArg(v_fst_2072_, v_fst_2081_);
lean_dec(v_fst_2081_);
v___x_2087_ = lean_array_get_size(v___x_2086_);
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_nat_dec_eq(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_del_object(v___x_2084_);
lean_del_object(v___x_2079_);
v___x_2090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__2);
v___x_2091_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___closed__5);
v___x_2092_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2090_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
lean_ctor_set(v___x_2092_, 2, v___x_2086_);
v___x_2093_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2092_, v_snd_2082_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
lean_dec_ref(v___x_2086_);
v___x_2094_ = lean_box(0);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2094_);
v___x_2096_ = v___x_2084_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_snd_2082_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2098_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2096_);
v___x_2098_ = v___x_2079_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v_fst_2072_);
v_a_2103_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2076_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2076_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2070_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2070_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns___boxed(lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec_ref(v_a_2119_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(size_t v_sz_2127_, size_t v_i_2128_, lean_object* v_bs_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___redArg(v_sz_2127_, v_i_2128_, v_bs_2129_, v___y_2131_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0___boxed(lean_object* v_sz_2138_, lean_object* v_i_2139_, lean_object* v_bs_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
size_t v_sz_boxed_2148_; size_t v_i_boxed_2149_; lean_object* v_res_2150_; 
v_sz_boxed_2148_ = lean_unbox_usize(v_sz_2138_);
lean_dec(v_sz_2138_);
v_i_boxed_2149_ = lean_unbox_usize(v_i_2139_);
lean_dec(v_i_2139_);
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns_spec__0(v_sz_boxed_2148_, v_i_boxed_2149_, v_bs_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2141_);
return v_res_2150_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(lean_object* v_x_2151_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg___boxed(lean_object* v_x_2153_){
_start:
{
uint8_t v_res_2154_; lean_object* v_r_2155_; 
v_res_2154_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___redArg(v_x_2153_);
lean_dec_ref(v_x_2153_);
v_r_2155_ = lean_box(v_res_2154_);
return v_r_2155_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(lean_object* v_00_u03b2_2156_, lean_object* v_x_2157_){
_start:
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0___boxed(lean_object* v_00_u03b2_2159_, lean_object* v_x_2160_){
_start:
{
uint8_t v_res_2161_; lean_object* v_r_2162_; 
v_res_2161_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__0(v_00_u03b2_2159_, v_x_2160_);
lean_dec_ref(v_x_2160_);
v_r_2162_ = lean_box(v_res_2161_);
return v_r_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(lean_object* v_as_2167_, size_t v_sz_2168_, size_t v_i_2169_, lean_object* v_b_2170_){
_start:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_usize_dec_lt(v_i_2169_, v_sz_2168_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_b_2170_);
return v___x_2173_;
}
else
{
lean_object* v_a_2174_; lean_object* v_fst_2175_; lean_object* v_snd_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2217_; 
v_a_2174_ = lean_array_uget(v_as_2167_, v_i_2169_);
v_fst_2175_ = lean_ctor_get(v_a_2174_, 0);
v_snd_2176_ = lean_ctor_get(v_a_2174_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_a_2174_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2178_ = v_a_2174_;
v_isShared_2179_ = v_isSharedCheck_2217_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snd_2176_);
lean_inc(v_fst_2175_);
lean_dec(v_a_2174_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2217_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; double v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_num_2186_; lean_object* v_den_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2216_; 
v___x_2180_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__1));
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2184_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2185_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2185_, 0, v___x_2181_);
lean_ctor_set(v___x_2185_, 1, v___x_2182_);
lean_ctor_set(v___x_2185_, 2, v___x_2184_);
lean_ctor_set_float(v___x_2185_, sizeof(void*)*3, v___x_2183_);
lean_ctor_set_float(v___x_2185_, sizeof(void*)*3 + 8, v___x_2183_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*3 + 16, v___x_2172_);
v_num_2186_ = lean_ctor_get(v_snd_2176_, 0);
v_den_2187_ = lean_ctor_get(v_snd_2176_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_snd_2176_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2189_ = v_snd_2176_;
v_isShared_2190_ = v_isSharedCheck_2216_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_den_2187_);
lean_inc(v_num_2186_);
lean_dec(v_snd_2176_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2216_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2191_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2175_);
v___x_2192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_Goal_ppENodeDecl___closed__3);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 7);
lean_ctor_set(v___x_2189_, 1, v___x_2192_);
lean_ctor_set(v___x_2189_, 0, v___x_2191_);
v___x_2194_ = v___x_2189_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___y_2196_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_dec_eq(v_den_2187_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2209_ = l_Int_repr(v_num_2186_);
lean_dec(v_num_2186_);
v___x_2210_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2));
v___x_2211_ = lean_string_append(v___x_2209_, v___x_2210_);
v___x_2212_ = l_Nat_reprFast(v_den_2187_);
v___x_2213_ = lean_string_append(v___x_2211_, v___x_2212_);
lean_dec_ref(v___x_2212_);
v___y_2196_ = v___x_2213_;
goto v___jp_2195_;
}
else
{
lean_object* v___x_2214_; 
lean_dec(v_den_2187_);
v___x_2214_ = l_Int_repr(v_num_2186_);
lean_dec(v_num_2186_);
v___y_2196_ = v___x_2214_;
goto v___jp_2195_;
}
v___jp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2196_);
v___x_2198_ = l_Lean_MessageData_ofFormat(v___x_2197_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set_tag(v___x_2178_, 7);
lean_ctor_set(v___x_2178_, 1, v___x_2198_);
lean_ctor_set(v___x_2178_, 0, v___x_2194_);
v___x_2200_ = v___x_2178_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; size_t v___x_2203_; size_t v___x_2204_; 
v___x_2201_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2185_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
lean_ctor_set(v___x_2201_, 2, v___x_2180_);
v___x_2202_ = lean_array_push(v_b_2170_, v___x_2201_);
v___x_2203_ = ((size_t)1ULL);
v___x_2204_ = lean_usize_add(v_i_2169_, v___x_2203_);
v_i_2169_ = v___x_2204_;
v_b_2170_ = v___x_2202_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___boxed(lean_object* v_as_2218_, lean_object* v_sz_2219_, lean_object* v_i_2220_, lean_object* v_b_2221_, lean_object* v___y_2222_){
_start:
{
size_t v_sz_boxed_2223_; size_t v_i_boxed_2224_; lean_object* v_res_2225_; 
v_sz_boxed_2223_ = lean_unbox_usize(v_sz_2219_);
lean_dec(v_sz_2219_);
v_i_boxed_2224_ = lean_unbox_usize(v_i_2220_);
lean_dec(v_i_2220_);
v_res_2225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_2218_, v_sz_boxed_2223_, v_i_boxed_2224_, v_b_2221_);
lean_dec_ref(v_as_2218_);
return v_res_2225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2(void){
_start:
{
lean_object* v___x_2229_; uint8_t v___x_2230_; double v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2229_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2230_ = 1;
v___x_2231_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2232_ = lean_box(0);
v___x_2233_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__1));
v___x_2234_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v___x_2232_);
lean_ctor_set(v___x_2234_, 2, v___x_2229_);
lean_ctor_set_float(v___x_2234_, sizeof(void*)*3, v___x_2231_);
lean_ctor_set_float(v___x_2234_, sizeof(void*)*3 + 8, v___x_2231_);
lean_ctor_set_uint8(v___x_2234_, sizeof(void*)*3 + 16, v___x_2230_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__4));
v___x_2239_ = l_Lean_MessageData_ofFormat(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(lean_object* v_goal_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_ref_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_ref_2246_ = lean_ctor_get(v_a_2243_, 2);
v___x_2247_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2248_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2247_, v_goal_2240_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2313_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2313_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2313_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v_vars_2253_; lean_object* v_varMap_2254_; lean_object* v_assignment_2255_; uint8_t v___x_2256_; 
v_vars_2253_ = lean_ctor_get(v_a_2249_, 0);
lean_inc_ref(v_vars_2253_);
v_varMap_2254_ = lean_ctor_get(v_a_2249_, 1);
lean_inc_ref(v_varMap_2254_);
v_assignment_2255_ = lean_ctor_get(v_a_2249_, 12);
lean_inc_ref(v_assignment_2255_);
lean_dec(v_a_2249_);
v___x_2256_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_varMap_2254_);
lean_dec_ref(v_varMap_2254_);
if (v___x_2256_ == 0)
{
lean_object* v_size_2257_; lean_object* v_size_2258_; uint8_t v___x_2259_; 
v_size_2257_ = lean_ctor_get(v_assignment_2255_, 2);
lean_inc(v_size_2257_);
lean_dec_ref(v_assignment_2255_);
v_size_2258_ = lean_ctor_get(v_vars_2253_, 2);
lean_inc(v_size_2258_);
lean_dec_ref(v_vars_2253_);
v___x_2259_ = lean_nat_dec_lt(v_size_2257_, v_size_2258_);
lean_dec(v_size_2258_);
lean_dec(v_size_2257_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_del_object(v___x_2251_);
v___x_2260_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(v_goal_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2296_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2296_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2296_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2265_ = lean_array_get_size(v_a_2261_);
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = lean_nat_dec_eq(v___x_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; size_t v_sz_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
lean_del_object(v___x_2263_);
v___x_2268_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v_sz_2269_ = lean_array_size(v_a_2261_);
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_a_2261_, v_sz_2269_, v___x_2270_, v___x_2268_);
lean_dec(v_a_2261_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2283_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2276_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__2);
v___x_2277_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___closed__5);
v___x_2278_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
lean_ctor_set(v___x_2278_, 2, v_a_2272_);
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2279_);
v___x_2281_ = v___x_2274_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
v_a_2284_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2271_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2271_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
lean_dec(v_a_2261_);
v___x_2292_ = lean_box(0);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2292_);
v___x_2294_ = v___x_2263_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
v_a_2297_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2260_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2260_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2305_ = lean_box(0);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2305_);
v___x_2307_ = v___x_2251_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
lean_dec_ref(v_assignment_2255_);
lean_dec_ref(v_vars_2253_);
v___x_2309_ = lean_box(0);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2309_);
v___x_2311_ = v___x_2251_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2325_; 
v_a_2314_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2316_ = v___x_2248_;
v_isShared_2317_ = v_isSharedCheck_2325_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2248_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2325_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2318_ = lean_io_error_to_string(v_a_2314_);
v___x_2319_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
v___x_2320_ = l_Lean_MessageData_ofFormat(v___x_2319_);
lean_inc(v_ref_2246_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v_ref_2246_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2321_);
v___x_2323_ = v___x_2316_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f___boxed(lean_object* v_goal_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(v_goal_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v_goal_2326_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(lean_object* v_as_2333_, size_t v_sz_2334_, size_t v_i_2335_, lean_object* v_b_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg(v_as_2333_, v_sz_2334_, v_i_2335_, v_b_2336_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___boxed(lean_object* v_as_2343_, lean_object* v_sz_2344_, lean_object* v_i_2345_, lean_object* v_b_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2344_);
lean_dec(v_sz_2344_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2345_);
lean_dec(v_i_2345_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1(v_as_2343_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_as_2343_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Meta_Grind_Arith_Cutsat_pp_x3f(v_a_2355_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2374_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2374_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2374_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
if (lean_obj_tag(v_a_2363_) == 1)
{
lean_object* v_val_2367_; lean_object* v___x_2368_; 
lean_del_object(v___x_2365_);
v_val_2367_ = lean_ctor_get(v_a_2363_, 0);
lean_inc(v_val_2367_);
lean_dec_ref_known(v_a_2363_, 1);
v___x_2368_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2367_, v_a_2356_);
return v___x_2368_;
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
lean_dec(v_a_2363_);
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v_a_2356_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2370_);
v___x_2372_ = v___x_2365_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v_a_2356_);
v_a_2375_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2362_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2362_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat___boxed(lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec_ref(v_a_2383_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(lean_object* v_rings_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(v_a_2392_, v_rings_2391_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2411_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2411_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2411_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
if (lean_obj_tag(v_a_2400_) == 1)
{
lean_object* v_val_2404_; lean_object* v___x_2405_; 
lean_del_object(v___x_2402_);
v_val_2404_ = lean_ctor_get(v_a_2400_, 0);
lean_inc(v_val_2404_);
lean_dec_ref_known(v_a_2400_, 1);
v___x_2405_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2404_, v_a_2393_);
return v___x_2405_;
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_dec(v_a_2400_);
v___x_2406_ = lean_box(0);
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v_a_2393_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2407_);
v___x_2409_ = v___x_2402_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_a_2393_);
v_a_2412_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2399_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2399_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing___boxed(lean_object* v_rings_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(v_rings_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec_ref(v_a_2421_);
lean_dec_ref(v_rings_2420_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_a_2429_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2448_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
if (lean_obj_tag(v_a_2437_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; 
lean_del_object(v___x_2439_);
v_val_2441_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v_a_2437_, 1);
v___x_2442_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2441_, v_a_2430_);
return v___x_2442_;
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_dec(v_a_2437_);
v___x_2443_ = lean_box(0);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v_a_2430_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2444_);
v___x_2446_ = v___x_2439_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
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
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec_ref(v_a_2430_);
v_a_2449_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2436_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2436_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith___boxed(lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec_ref(v_a_2457_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_Meta_Grind_AC_pp_x3f(v_a_2465_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2484_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2484_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2484_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
if (lean_obj_tag(v_a_2473_) == 1)
{
lean_object* v_val_2477_; lean_object* v___x_2478_; 
lean_del_object(v___x_2475_);
v_val_2477_ = lean_ctor_get(v_a_2473_, 0);
lean_inc(v_val_2477_);
lean_dec_ref_known(v_a_2473_, 1);
v___x_2478_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v_val_2477_, v_a_2466_);
return v___x_2478_;
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_dec(v_a_2473_);
v___x_2479_ = lean_box(0);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v_a_2466_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2480_);
v___x_2482_ = v___x_2475_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
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
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v_a_2466_);
v_a_2485_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2472_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2472_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC___boxed(lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec_ref(v_a_2493_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(lean_object* v_a_2501_, lean_object* v_as_2502_, size_t v_i_2503_, size_t v_stop_2504_, lean_object* v_b_2505_){
_start:
{
lean_object* v___y_2507_; uint8_t v___x_2511_; 
v___x_2511_ = lean_usize_dec_eq(v_i_2503_, v_stop_2504_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_array_uget_borrowed(v_as_2502_, v_i_2503_);
v___x_2513_ = l_Lean_Meta_Grind_Goal_getENode_x3f(v_a_2501_, v___x_2512_);
if (lean_obj_tag(v___x_2513_) == 1)
{
lean_object* v_val_2514_; lean_object* v_generation_2515_; uint8_t v___x_2516_; 
v_val_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v_generation_2515_ = lean_ctor_get(v_val_2514_, 8);
lean_inc(v_generation_2515_);
lean_dec(v_val_2514_);
v___x_2516_ = lean_nat_dec_le(v_b_2505_, v_generation_2515_);
if (v___x_2516_ == 0)
{
lean_dec(v_generation_2515_);
v___y_2507_ = v_b_2505_;
goto v___jp_2506_;
}
else
{
lean_dec(v_b_2505_);
v___y_2507_ = v_generation_2515_;
goto v___jp_2506_;
}
}
else
{
lean_dec(v___x_2513_);
v___y_2507_ = v_b_2505_;
goto v___jp_2506_;
}
}
else
{
return v_b_2505_;
}
v___jp_2506_:
{
size_t v___x_2508_; size_t v___x_2509_; 
v___x_2508_ = ((size_t)1ULL);
v___x_2509_ = lean_usize_add(v_i_2503_, v___x_2508_);
v_i_2503_ = v___x_2509_;
v_b_2505_ = v___y_2507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1___boxed(lean_object* v_a_2517_, lean_object* v_as_2518_, lean_object* v_i_2519_, lean_object* v_stop_2520_, lean_object* v_b_2521_){
_start:
{
size_t v_i_boxed_2522_; size_t v_stop_boxed_2523_; lean_object* v_res_2524_; 
v_i_boxed_2522_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_stop_boxed_2523_ = lean_unbox_usize(v_stop_2520_);
lean_dec(v_stop_2520_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2517_, v_as_2518_, v_i_boxed_2522_, v_stop_boxed_2523_, v_b_2521_);
lean_dec_ref(v_as_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(lean_object* v_a_2525_, lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2526_) == 0)
{
lean_object* v_cs_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_cs_2528_ = lean_ctor_get(v_x_2526_, 0);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_array_get_size(v_cs_2528_);
v___x_2531_ = lean_nat_dec_lt(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
return v_x_2527_;
}
else
{
size_t v___x_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = lean_usize_of_nat(v___x_2530_);
v___x_2534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2525_, v_cs_2528_, v___x_2532_, v___x_2533_, v_x_2527_);
return v___x_2534_;
}
}
else
{
lean_object* v_vs_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v_vs_2535_ = lean_ctor_get(v_x_2526_, 0);
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2537_ = lean_array_get_size(v_vs_2535_);
v___x_2538_ = lean_nat_dec_lt(v___x_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
return v_x_2527_;
}
else
{
size_t v___x_2539_; size_t v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = lean_usize_of_nat(v___x_2537_);
v___x_2541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2525_, v_vs_2535_, v___x_2539_, v___x_2540_, v_x_2527_);
return v___x_2541_;
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
v___x_2565_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = lean_usize_of_nat(v___x_2584_);
lean_dec(v___x_2584_);
v___x_2588_ = lean_usize_of_nat(v___x_2585_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0_spec__1(v_a_2566_, v_cs_2571_, v___x_2587_, v___x_2588_, v___x_2582_);
return v___x_2589_;
}
}
else
{
lean_object* v_vs_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_vs_2590_ = lean_ctor_get(v_x_2567_, 0);
v___x_2591_ = lean_usize_to_nat(v_x_2568_);
v___x_2592_ = lean_array_get_size(v_vs_2590_);
v___x_2593_ = lean_nat_dec_lt(v___x_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_dec(v___x_2591_);
return v_x_2570_;
}
else
{
size_t v___x_2594_; size_t v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_usize_of_nat(v___x_2591_);
lean_dec(v___x_2591_);
v___x_2595_ = lean_usize_of_nat(v___x_2592_);
v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2566_, v_vs_2590_, v___x_2594_, v___x_2595_, v_x_2570_);
return v___x_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0___boxed(lean_object* v_a_2597_, lean_object* v_x_2598_, lean_object* v_x_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_){
_start:
{
size_t v_x_7552__boxed_2602_; size_t v_x_7553__boxed_2603_; lean_object* v_res_2604_; 
v_x_7552__boxed_2602_ = lean_unbox_usize(v_x_2599_);
lean_dec(v_x_2599_);
v_x_7553__boxed_2603_ = lean_unbox_usize(v_x_2600_);
lean_dec(v_x_2600_);
v_res_2604_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__0(v_a_2597_, v_x_2598_, v_x_7552__boxed_2602_, v_x_7553__boxed_2603_, v_x_2601_);
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
size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = lean_usize_of_nat(v___x_2618_);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2612_, v___x_2620_, v___x_2621_, v___x_2617_);
return v___x_2622_;
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2623_ = lean_nat_sub(v_start_2608_, v_tailOff_2614_);
v___x_2624_ = lean_array_get_size(v_tail_2612_);
v___x_2625_ = lean_nat_dec_lt(v___x_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_dec(v___x_2623_);
return v_init_2607_;
}
else
{
size_t v___x_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_usize_of_nat(v___x_2623_);
lean_dec(v___x_2623_);
v___x_2627_ = lean_usize_of_nat(v___x_2624_);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2612_, v___x_2626_, v___x_2627_, v_init_2607_);
return v___x_2628_;
}
}
}
else
{
lean_object* v_root_2629_; lean_object* v_tail_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v_root_2629_ = lean_ctor_get(v_t_2606_, 0);
v_tail_2630_ = lean_ctor_get(v_t_2606_, 1);
v___x_2631_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__2(v_a_2605_, v_root_2629_, v_init_2607_);
v___x_2632_ = lean_array_get_size(v_tail_2630_);
v___x_2633_ = lean_nat_dec_lt(v___x_2609_, v___x_2632_);
if (v___x_2633_ == 0)
{
return v___x_2631_;
}
else
{
size_t v___x_2634_; size_t v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((size_t)0ULL);
v___x_2635_ = lean_usize_of_nat(v___x_2632_);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0_spec__1(v_a_2605_, v_tail_2630_, v___x_2634_, v___x_2635_, v___x_2631_);
return v___x_2636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0___boxed(lean_object* v_a_2637_, lean_object* v_t_2638_, lean_object* v_init_2639_, lean_object* v_start_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_2637_, v_t_2638_, v_init_2639_, v_start_2640_);
lean_dec(v_start_2640_);
lean_dec_ref(v_t_2638_);
lean_dec_ref(v_a_2637_);
return v_res_2641_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2(void){
_start:
{
lean_object* v___x_2645_; uint8_t v___x_2646_; double v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2645_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2646_ = 1;
v___x_2647_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2648_ = lean_box(0);
v___x_2649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__1));
v___x_2650_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v___x_2648_);
lean_ctor_set(v___x_2650_, 2, v___x_2645_);
lean_ctor_set_float(v___x_2650_, sizeof(void*)*3, v___x_2647_);
lean_ctor_set_float(v___x_2650_, sizeof(void*)*3 + 8, v___x_2647_);
lean_ctor_set_uint8(v___x_2650_, sizeof(void*)*3 + 16, v___x_2646_);
return v___x_2650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__4));
v___x_2655_ = l_Lean_MessageData_ofFormat(v___x_2654_);
return v___x_2655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__8));
v___x_2661_ = l_Lean_stringToMessageData(v___x_2660_);
return v___x_2661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__10));
v___x_2664_ = l_Lean_stringToMessageData(v___x_2663_);
return v___x_2664_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__13(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__12));
v___x_2667_ = l_Lean_stringToMessageData(v___x_2666_);
return v___x_2667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__14));
v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
return v___x_2670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__16));
v___x_2673_ = l_Lean_stringToMessageData(v___x_2672_);
return v___x_2673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__19(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__18));
v___x_2676_ = l_Lean_stringToMessageData(v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(lean_object* v_c_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_toGoalState_2682_; lean_object* v_exprs_2683_; lean_object* v_ematch_2684_; lean_object* v_split_2685_; lean_object* v___x_2686_; lean_object* v_msgs_2688_; lean_object* v___y_2689_; lean_object* v___x_2699_; lean_object* v_splits_2700_; lean_object* v_ematch_2701_; lean_object* v_gen_2702_; lean_object* v_instances_2703_; lean_object* v_liaSteps_2704_; lean_object* v_numInstances_2705_; lean_object* v_num_2706_; lean_object* v___x_2707_; lean_object* v_msgs_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v_msgs_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v_msgs_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v_msgs_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; uint8_t v___x_2816_; 
v_toGoalState_2682_ = lean_ctor_get(v_a_2678_, 0);
v_exprs_2683_ = lean_ctor_get(v_toGoalState_2682_, 2);
v_ematch_2684_ = lean_ctor_get(v_toGoalState_2682_, 13);
v_split_2685_ = lean_ctor_get(v_toGoalState_2682_, 15);
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2699_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds_spec__0(v_a_2678_, v_exprs_2683_, v___x_2686_, v___x_2686_);
v_splits_2700_ = lean_ctor_get(v_c_2677_, 0);
v_ematch_2701_ = lean_ctor_get(v_c_2677_, 1);
v_gen_2702_ = lean_ctor_get(v_c_2677_, 2);
v_instances_2703_ = lean_ctor_get(v_c_2677_, 4);
v_liaSteps_2704_ = lean_ctor_get(v_c_2677_, 9);
lean_inc(v_liaSteps_2704_);
v_numInstances_2705_ = lean_ctor_get(v_ematch_2684_, 4);
v_num_2706_ = lean_ctor_get(v_ematch_2684_, 6);
v___x_2707_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2816_ = lean_nat_dec_le(v_instances_2703_, v_numInstances_2705_);
if (v___x_2816_ == 0)
{
v_msgs_2798_ = v___x_2707_;
v___y_2799_ = v_a_2679_;
v___y_2800_ = v_a_2680_;
goto v___jp_2797_;
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; double v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2820_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2821_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2821_, 0, v___x_2817_);
lean_ctor_set(v___x_2821_, 1, v___x_2818_);
lean_ctor_set(v___x_2821_, 2, v___x_2820_);
lean_ctor_set_float(v___x_2821_, sizeof(void*)*3, v___x_2819_);
lean_ctor_set_float(v___x_2821_, sizeof(void*)*3 + 8, v___x_2819_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*3 + 16, v___x_2816_);
v___x_2822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__19, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__19);
lean_inc(v_instances_2703_);
v___x_2823_ = l_Nat_reprFast(v_instances_2703_);
v___x_2824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
v___x_2825_ = l_Lean_MessageData_ofFormat(v___x_2824_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2822_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2821_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
lean_ctor_set(v___x_2829_, 2, v___x_2707_);
v___x_2830_ = lean_array_push(v___x_2707_, v___x_2829_);
v_msgs_2798_ = v___x_2830_;
v___y_2799_ = v_a_2679_;
v___y_2800_ = v_a_2680_;
goto v___jp_2797_;
}
v___jp_2687_:
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = lean_array_get_size(v_msgs_2688_);
v___x_2691_ = lean_nat_dec_eq(v___x_2690_, v___x_2686_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2692_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__2);
v___x_2693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__5);
v___x_2694_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
lean_ctor_set(v___x_2694_, 2, v_msgs_2688_);
v___x_2695_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2694_, v___y_2689_);
return v___x_2695_;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v_msgs_2688_);
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v___y_2689_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
}
v___jp_2708_:
{
lean_object* v_ref_2712_; lean_object* v___x_2713_; 
v_ref_2712_ = lean_ctor_get(v___y_2711_, 2);
v___x_2713_ = l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(v_a_2678_, v_c_2677_, v_msgs_2709_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2715_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2716_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2715_, v_a_2678_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v_steps_2718_; uint8_t v___x_2719_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v_steps_2718_ = lean_ctor_get(v_a_2717_, 14);
lean_inc(v_steps_2718_);
lean_dec(v_a_2717_);
v___x_2719_ = lean_nat_dec_le(v_liaSteps_2704_, v_steps_2718_);
lean_dec(v_steps_2718_);
if (v___x_2719_ == 0)
{
lean_dec(v_liaSteps_2704_);
v_msgs_2688_ = v_a_2714_;
v___y_2689_ = v___y_2710_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; double v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2723_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2724_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2724_, 0, v___x_2720_);
lean_ctor_set(v___x_2724_, 1, v___x_2721_);
lean_ctor_set(v___x_2724_, 2, v___x_2723_);
lean_ctor_set_float(v___x_2724_, sizeof(void*)*3, v___x_2722_);
lean_ctor_set_float(v___x_2724_, sizeof(void*)*3 + 8, v___x_2722_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*3 + 16, v___x_2719_);
v___x_2725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__9);
v___x_2726_ = l_Nat_reprFast(v_liaSteps_2704_);
v___x_2727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
v___x_2728_ = l_Lean_MessageData_ofFormat(v___x_2727_);
v___x_2729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2725_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2724_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
lean_ctor_set(v___x_2732_, 2, v___x_2707_);
v___x_2733_ = lean_array_push(v_a_2714_, v___x_2732_);
v_msgs_2688_ = v___x_2733_;
v___y_2689_ = v___y_2710_;
goto v___jp_2687_;
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2714_);
lean_dec_ref(v___y_2710_);
lean_dec(v_liaSteps_2704_);
v_a_2734_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2736_ = v___x_2716_;
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2716_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2738_ = lean_io_error_to_string(v_a_2734_);
v___x_2739_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
v___x_2740_ = l_Lean_MessageData_ofFormat(v___x_2739_);
lean_inc(v_ref_2712_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_ref_2712_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2741_);
v___x_2743_ = v___x_2736_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2757_; 
lean_dec_ref(v___y_2710_);
lean_dec(v_liaSteps_2704_);
v_a_2746_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2748_ = v___x_2713_;
v_isShared_2749_ = v_isSharedCheck_2757_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2713_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2757_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2750_ = lean_io_error_to_string(v_a_2746_);
v___x_2751_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
v___x_2752_ = l_Lean_MessageData_ofFormat(v___x_2751_);
lean_inc(v_ref_2712_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_ref_2712_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2753_);
v___x_2755_ = v___x_2748_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
v___jp_2758_:
{
uint8_t v___x_2762_; 
v___x_2762_ = lean_nat_dec_le(v_gen_2702_, v___x_2699_);
lean_dec(v___x_2699_);
if (v___x_2762_ == 0)
{
v_msgs_2709_ = v_msgs_2759_;
v___y_2710_ = v___y_2760_;
v___y_2711_ = v___y_2761_;
goto v___jp_2708_;
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
lean_inc(v_gen_2702_);
v___x_2769_ = l_Nat_reprFast(v_gen_2702_);
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
lean_ctor_set(v___x_2775_, 2, v___x_2707_);
v___x_2776_ = lean_array_push(v_msgs_2759_, v___x_2775_);
v_msgs_2709_ = v___x_2776_;
v___y_2710_ = v___y_2760_;
v___y_2711_ = v___y_2761_;
goto v___jp_2708_;
}
}
v___jp_2777_:
{
lean_object* v_num_2781_; uint8_t v___x_2782_; 
v_num_2781_ = lean_ctor_get(v_split_2685_, 0);
v___x_2782_ = lean_nat_dec_le(v_splits_2700_, v_num_2781_);
if (v___x_2782_ == 0)
{
v_msgs_2759_ = v_msgs_2778_;
v___y_2760_ = v___y_2779_;
v___y_2761_ = v___y_2780_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; double v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2784_ = lean_box(0);
v___x_2785_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2786_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2787_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2787_, 0, v___x_2783_);
lean_ctor_set(v___x_2787_, 1, v___x_2784_);
lean_ctor_set(v___x_2787_, 2, v___x_2786_);
lean_ctor_set_float(v___x_2787_, sizeof(void*)*3, v___x_2785_);
lean_ctor_set_float(v___x_2787_, sizeof(void*)*3 + 8, v___x_2785_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*3 + 16, v___x_2782_);
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__15);
lean_inc(v_splits_2700_);
v___x_2789_ = l_Nat_reprFast(v_splits_2700_);
v___x_2790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
v___x_2791_ = l_Lean_MessageData_ofFormat(v___x_2790_);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2788_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2787_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
lean_ctor_set(v___x_2795_, 2, v___x_2707_);
v___x_2796_ = lean_array_push(v_msgs_2778_, v___x_2795_);
v_msgs_2759_ = v___x_2796_;
v___y_2760_ = v___y_2779_;
v___y_2761_ = v___y_2780_;
goto v___jp_2758_;
}
}
v___jp_2797_:
{
uint8_t v___x_2801_; 
v___x_2801_ = lean_nat_dec_le(v_ematch_2701_, v_num_2706_);
if (v___x_2801_ == 0)
{
v_msgs_2778_ = v_msgs_2798_;
v___y_2779_ = v___y_2799_;
v___y_2780_ = v___y_2800_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2803_; double v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__7));
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2805_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2806_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2806_, 0, v___x_2802_);
lean_ctor_set(v___x_2806_, 1, v___x_2803_);
lean_ctor_set(v___x_2806_, 2, v___x_2805_);
lean_ctor_set_float(v___x_2806_, sizeof(void*)*3, v___x_2804_);
lean_ctor_set_float(v___x_2806_, sizeof(void*)*3 + 8, v___x_2804_);
lean_ctor_set_uint8(v___x_2806_, sizeof(void*)*3 + 16, v___x_2801_);
v___x_2807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__17);
lean_inc(v_ematch_2701_);
v___x_2808_ = l_Nat_reprFast(v_ematch_2701_);
v___x_2809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
v___x_2810_ = l_Lean_MessageData_ofFormat(v___x_2809_);
v___x_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2807_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___closed__11);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2806_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
lean_ctor_set(v___x_2814_, 2, v___x_2707_);
v___x_2815_ = lean_array_push(v_msgs_2798_, v___x_2814_);
v_msgs_2778_ = v___x_2815_;
v___y_2779_ = v___y_2799_;
v___y_2780_ = v___y_2800_;
goto v___jp_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg___boxed(lean_object* v_c_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_c_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
lean_dec_ref(v_a_2834_);
lean_dec_ref(v_a_2832_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(lean_object* v_c_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_c_2837_, v_a_2838_, v_a_2839_, v_a_2842_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___boxed(lean_object* v_c_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds(v_c_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec_ref(v_a_2847_);
return v_res_2854_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2858_; uint8_t v___x_2859_; double v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2858_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_2859_ = 1;
v___x_2860_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_2861_ = lean_box(0);
v___x_2862_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__1));
v___x_2863_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set(v___x_2863_, 1, v___x_2861_);
lean_ctor_set(v___x_2863_, 2, v___x_2858_);
lean_ctor_set_float(v___x_2863_, sizeof(void*)*3, v___x_2860_);
lean_ctor_set_float(v___x_2863_, sizeof(void*)*3 + 8, v___x_2860_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*3 + 16, v___x_2859_);
return v___x_2863_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__3));
v___x_2866_ = l_Lean_stringToMessageData(v___x_2865_);
return v___x_2866_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_pp_x3f_spec__1___redArg___closed__2));
v___x_2868_ = l_Lean_stringToMessageData(v___x_2867_);
return v___x_2868_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__6));
v___x_2871_ = l_Lean_stringToMessageData(v___x_2870_);
return v___x_2871_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__8));
v___x_2874_ = l_Lean_stringToMessageData(v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(lean_object* v_as_x27_2875_, lean_object* v_b_2876_, lean_object* v___y_2877_){
_start:
{
if (lean_obj_tag(v_as_x27_2875_) == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2879_, 0, v_b_2876_);
lean_ctor_set(v___x_2879_, 1, v___y_2877_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
else
{
lean_object* v_head_2881_; lean_object* v_tail_2882_; lean_object* v_expr_2883_; lean_object* v_i_2884_; lean_object* v_num_2885_; lean_object* v_source_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v_head_2881_ = lean_ctor_get(v_as_x27_2875_, 0);
v_tail_2882_ = lean_ctor_get(v_as_x27_2875_, 1);
v_expr_2883_ = lean_ctor_get(v_head_2881_, 0);
v_i_2884_ = lean_ctor_get(v_head_2881_, 1);
v_num_2885_ = lean_ctor_get(v_head_2881_, 2);
v_source_2886_ = lean_ctor_get(v_head_2881_, 3);
v___x_2887_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_2888_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
v___x_2889_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__4);
v___x_2890_ = lean_unsigned_to_nat(1u);
v___x_2891_ = lean_nat_add(v_i_2884_, v___x_2890_);
v___x_2892_ = l_Nat_reprFast(v___x_2891_);
v___x_2893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
v___x_2894_ = l_Lean_MessageData_ofFormat(v___x_2893_);
v___x_2895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2889_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__5);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
lean_inc(v_num_2885_);
v___x_2898_ = l_Nat_reprFast(v_num_2885_);
v___x_2899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
v___x_2900_ = l_Lean_MessageData_ofFormat(v___x_2899_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2897_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__7);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
lean_inc_ref(v_expr_2883_);
v___x_2904_ = l_Lean_MessageData_ofExpr(v_expr_2883_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__9);
lean_inc(v_source_2886_);
v___x_2907_ = l_Lean_Meta_Grind_SplitSource_toMessageData(v_source_2886_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2888_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
lean_ctor_set(v___x_2909_, 2, v___x_2887_);
v___x_2910_ = lean_mk_empty_array_with_capacity(v___x_2890_);
v___x_2911_ = lean_array_push(v___x_2910_, v___x_2909_);
v___x_2912_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2888_);
lean_ctor_set(v___x_2912_, 1, v___x_2905_);
lean_ctor_set(v___x_2912_, 2, v___x_2911_);
v___x_2913_ = lean_array_push(v_b_2876_, v___x_2912_);
v_as_x27_2875_ = v_tail_2882_;
v_b_2876_ = v___x_2913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___boxed(lean_object* v_as_x27_2915_, lean_object* v_b_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_2915_, v_b_2916_, v___y_2917_);
lean_dec(v_as_x27_2915_);
return v_res_2919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__1));
v___x_2924_ = l_Lean_MessageData_ofFormat(v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_toGoalState_2932_; lean_object* v_split_2933_; lean_object* v_trace_2934_; uint8_t v___x_2935_; 
v_toGoalState_2932_ = lean_ctor_get(v_a_2925_, 0);
v_split_2933_ = lean_ctor_get(v_toGoalState_2932_, 15);
v_trace_2934_ = lean_ctor_get(v_split_2933_, 4);
v___x_2935_ = l_List_isEmpty___redArg(v_trace_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v_a_2939_; lean_object* v_fst_2940_; lean_object* v_snd_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2936_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
lean_inc(v_trace_2934_);
v___x_2937_ = l_List_reverse___redArg(v_trace_2934_);
v___x_2938_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v___x_2937_, v___x_2936_, v_a_2926_);
lean_dec(v___x_2937_);
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v_fst_2940_ = lean_ctor_get(v_a_2939_, 0);
lean_inc(v_fst_2940_);
v_snd_2941_ = lean_ctor_get(v_a_2939_, 1);
lean_inc(v_snd_2941_);
lean_dec(v_a_2939_);
v___x_2942_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg___closed__2);
v___x_2943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2, &l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___closed__2);
v___x_2944_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
lean_ctor_set(v___x_2944_, 2, v_fst_2940_);
v___x_2945_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_2944_, v_snd_2941_);
return v___x_2945_;
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = lean_box(0);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v_a_2926_);
v___x_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace___boxed(lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec_ref(v_a_2949_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(lean_object* v_as_2957_, lean_object* v_as_x27_2958_, lean_object* v_b_2959_, lean_object* v_a_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___redArg(v_as_x27_2958_, v_b_2959_, v___y_2962_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0___boxed(lean_object* v_as_2969_, lean_object* v_as_x27_2970_, lean_object* v_b_2971_, lean_object* v_a_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace_spec__0(v_as_2969_, v_as_x27_2970_, v_b_2971_, v_a_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec_ref(v___y_2973_);
lean_dec(v_as_x27_2970_);
lean_dec(v_as_2969_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(lean_object* v_goal_2985_, lean_object* v_config_2986_, lean_object* v_rings_2987_, uint8_t v_collapsedMain_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_toGoalState_2996_; lean_object* v_facts_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v_a_3004_; lean_object* v_snd_3005_; lean_object* v___x_3006_; 
v_toGoalState_2996_ = lean_ctor_get(v_goal_2985_, 0);
v_facts_2997_ = lean_ctor_get(v_toGoalState_2996_, 11);
v___x_2998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__1));
v___x_2999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___closed__2));
v___x_3000_ = l_Lean_PersistentArray_toArray___redArg(v_facts_2997_);
v___x_3001_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs_spec__6___redArg___closed__2));
v___x_3002_ = l_Lean_Meta_Grind_ppExprArray(v___x_2998_, v___x_2999_, v___x_3000_, v___x_3001_, v_collapsedMain_2988_);
v___x_3003_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_pushMsg___redArg(v___x_3002_, v_a_2990_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v_snd_3005_ = lean_ctor_get(v_a_3004_, 1);
lean_inc(v_snd_3005_);
lean_dec(v_a_3004_);
v___x_3006_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppEqcs(v_collapsedMain_2988_, v_a_2989_, v_snd_3005_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_snd_3008_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v_snd_3008_ = lean_ctor_get(v_a_3007_, 1);
lean_inc(v_snd_3008_);
lean_dec(v_a_3007_);
v___x_3009_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCasesTrace(v_a_2989_, v_snd_3008_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v_snd_3011_; lean_object* v___x_3012_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v_snd_3011_ = lean_ctor_get(v_a_3010_, 1);
lean_inc(v_snd_3011_);
lean_dec(v_a_3010_);
v___x_3012_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppActiveTheoremPatterns(v_a_2989_, v_snd_3011_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v_snd_3014_; lean_object* v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v_snd_3014_ = lean_ctor_get(v_a_3013_, 1);
lean_inc(v_snd_3014_);
lean_dec(v_a_3013_);
v___x_3015_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCutsat(v_a_2989_, v_snd_3014_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v_snd_3017_; lean_object* v___x_3018_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v_snd_3017_ = lean_ctor_get(v_a_3016_, 1);
lean_inc(v_snd_3017_);
lean_dec(v_a_3016_);
v___x_3018_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppLinarith(v_a_2989_, v_snd_3017_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v_snd_3020_; lean_object* v___x_3021_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v_snd_3020_ = lean_ctor_get(v_a_3019_, 1);
lean_inc(v_snd_3020_);
lean_dec(v_a_3019_);
v___x_3021_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppCommRing(v_rings_2987_, v_a_2989_, v_snd_3020_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v_snd_3023_; lean_object* v___x_3024_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v_snd_3023_ = lean_ctor_get(v_a_3022_, 1);
lean_inc(v_snd_3023_);
lean_dec(v_a_3022_);
v___x_3024_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppAC(v_a_2989_, v_snd_3023_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v_snd_3026_; lean_object* v___x_3027_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v_snd_3026_ = lean_ctor_get(v_a_3025_, 1);
lean_inc(v_snd_3026_);
lean_dec(v_a_3025_);
v___x_3027_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_ppThresholds___redArg(v_config_2986_, v_a_2989_, v_snd_3026_, v_a_2993_);
return v___x_3027_;
}
else
{
lean_dec_ref(v_config_2986_);
return v___x_3024_;
}
}
else
{
lean_dec_ref(v_config_2986_);
return v___x_3021_;
}
}
else
{
lean_dec_ref(v_config_2986_);
return v___x_3018_;
}
}
else
{
lean_dec_ref(v_config_2986_);
return v___x_3015_;
}
}
else
{
lean_dec_ref(v_config_2986_);
return v___x_3012_;
}
}
else
{
lean_dec_ref(v_config_2986_);
return v___x_3009_;
}
}
else
{
lean_dec_ref(v_config_2986_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go___boxed(lean_object* v_goal_3028_, lean_object* v_config_3029_, lean_object* v_rings_3030_, lean_object* v_collapsedMain_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
uint8_t v_collapsedMain_boxed_3039_; lean_object* v_res_3040_; 
v_collapsedMain_boxed_3039_ = lean_unbox(v_collapsedMain_3031_);
v_res_3040_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_3028_, v_config_3029_, v_rings_3030_, v_collapsedMain_boxed_3039_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec_ref(v_a_3032_);
lean_dec_ref(v_rings_3030_);
lean_dec_ref(v_goal_3028_);
return v_res_3040_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2(void){
_start:
{
lean_object* v___x_3044_; uint8_t v___x_3045_; double v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3044_ = ((lean_object*)(l_Lean_Meta_Grind_ppGoals___closed__0));
v___x_3045_ = 0;
v___x_3046_ = lean_float_once(&l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0, &l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0_once, _init_l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__0);
v___x_3047_ = lean_box(0);
v___x_3048_ = ((lean_object*)(l_Lean_Meta_Grind_goalDiagToMessageData___closed__1));
v___x_3049_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v___x_3047_);
lean_ctor_set(v___x_3049_, 2, v___x_3044_);
lean_ctor_set_float(v___x_3049_, sizeof(void*)*3, v___x_3046_);
lean_ctor_set_float(v___x_3049_, sizeof(void*)*3 + 8, v___x_3046_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*3 + 16, v___x_3045_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData(lean_object* v_goal_3050_, lean_object* v_config_3051_, lean_object* v_rings_3052_, lean_object* v_header_3053_, uint8_t v_collapsedMain_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Lean_toTraceElem___at___00Lean_Meta_Grind_ppExprArray_spec__0___closed__1));
v___x_3061_ = l___private_Lean_Meta_Tactic_Grind_PP_0__Lean_Meta_Grind_goalDiagToMessageData_go(v_goal_3050_, v_config_3051_, v_rings_3052_, v_collapsedMain_3054_, v_goal_3050_, v___x_3060_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3074_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3074_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3074_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v_snd_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3072_; 
v_snd_3066_ = lean_ctor_get(v_a_3062_, 1);
lean_inc(v_snd_3066_);
lean_dec(v_a_3062_);
v___x_3067_ = lean_obj_once(&l_Lean_Meta_Grind_goalDiagToMessageData___closed__2, &l_Lean_Meta_Grind_goalDiagToMessageData___closed__2_once, _init_l_Lean_Meta_Grind_goalDiagToMessageData___closed__2);
v___x_3068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3068_, 0, v_header_3053_);
v___x_3069_ = l_Lean_MessageData_ofFormat(v___x_3068_);
v___x_3070_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3067_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
lean_ctor_set(v___x_3070_, 2, v_snd_3066_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v___x_3070_);
v___x_3072_ = v___x_3064_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v_header_3053_);
v_a_3075_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3061_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3061_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalDiagToMessageData___boxed(lean_object* v_goal_3083_, lean_object* v_config_3084_, lean_object* v_rings_3085_, lean_object* v_header_3086_, lean_object* v_collapsedMain_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
uint8_t v_collapsedMain_boxed_3093_; lean_object* v_res_3094_; 
v_collapsedMain_boxed_3093_ = lean_unbox(v_collapsedMain_3087_);
v_res_3094_ = l_Lean_Meta_Grind_goalDiagToMessageData(v_goal_3083_, v_config_3084_, v_rings_3085_, v_header_3086_, v_collapsedMain_boxed_3093_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec_ref(v_rings_3085_);
lean_dec_ref(v_goal_3083_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(lean_object* v_msgData_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v_env_3102_; uint8_t v___x_3103_; lean_object* v_env_3104_; lean_object* v___x_3105_; lean_object* v_toCold_3106_; lean_object* v_mctx_3107_; lean_object* v_lctx_3108_; lean_object* v_options_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3101_ = lean_st_ref_get(v___y_3099_);
v_env_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc_ref(v_env_3102_);
lean_dec(v___x_3101_);
v___x_3103_ = 0;
v_env_3104_ = l_Lean_Environment_setRecordingDeps(v_env_3102_, v___x_3103_);
v___x_3105_ = lean_st_ref_get(v___y_3097_);
v_toCold_3106_ = lean_ctor_get(v___y_3098_, 0);
v_mctx_3107_ = lean_ctor_get(v___x_3105_, 0);
lean_inc_ref(v_mctx_3107_);
lean_dec(v___x_3105_);
v_lctx_3108_ = lean_ctor_get(v___y_3096_, 2);
v_options_3109_ = lean_ctor_get(v_toCold_3106_, 2);
lean_inc_ref(v_options_3109_);
lean_inc_ref(v_lctx_3108_);
v___x_3110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3110_, 0, v_env_3104_);
lean_ctor_set(v___x_3110_, 1, v_mctx_3107_);
lean_ctor_set(v___x_3110_, 2, v_lctx_3108_);
lean_ctor_set(v___x_3110_, 3, v_options_3109_);
v___x_3111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v_msgData_3095_);
v___x_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0___boxed(lean_object* v_msgData_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(v_msgData_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(lean_object* v_mvarId_3120_, lean_object* v_x_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3120_, v_x_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3127_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3127_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg___boxed(lean_object* v_mvarId_3144_, lean_object* v_x_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3144_, v_x_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(lean_object* v_00_u03b1_3152_, lean_object* v_mvarId_3153_, lean_object* v_x_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3153_, v_x_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___boxed(lean_object* v_00_u03b1_3161_, lean_object* v_mvarId_3162_, lean_object* v_x_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1(v_00_u03b1_3161_, v_mvarId_3162_, v_x_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v_res_3169_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Goal_ppState_spec__2___redArg___closed__0));
v___x_3172_ = l_Lean_stringToMessageData(v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0(uint8_t v_verbose_3173_, lean_object* v_mvarId_3174_, lean_object* v_goal_3175_, lean_object* v_config_3176_, lean_object* v_rings_3177_, uint8_t v___x_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
if (v_verbose_3173_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_dec_ref(v_config_3176_);
v___x_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3184_, 0, v_mvarId_3174_);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
return v___x_3185_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__0));
v___x_3187_ = l_Lean_Meta_Grind_goalDiagToMessageData(v_goal_3175_, v_config_3176_, v_rings_3177_, v___x_3186_, v___x_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3199_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3199_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3199_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
lean_ctor_set_tag(v___x_3190_, 1);
lean_ctor_set(v___x_3190_, 0, v_mvarId_3174_);
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_mvarId_3174_);
v___x_3193_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3194_ = lean_obj_once(&l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1, &l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_goalToMessageData___lam__0___closed__1);
v___x_3195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v_a_3188_);
v___x_3197_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Grind_goalToMessageData_spec__0(v___x_3196_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
return v___x_3197_;
}
}
}
else
{
lean_dec(v_mvarId_3174_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed(lean_object* v_verbose_3200_, lean_object* v_mvarId_3201_, lean_object* v_goal_3202_, lean_object* v_config_3203_, lean_object* v_rings_3204_, lean_object* v___x_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
uint8_t v_verbose_boxed_3211_; uint8_t v___x_1165__boxed_3212_; lean_object* v_res_3213_; 
v_verbose_boxed_3211_ = lean_unbox(v_verbose_3200_);
v___x_1165__boxed_3212_ = lean_unbox(v___x_3205_);
v_res_3213_ = l_Lean_Meta_Grind_goalToMessageData___lam__0(v_verbose_boxed_3211_, v_mvarId_3201_, v_goal_3202_, v_config_3203_, v_rings_3204_, v___x_1165__boxed_3212_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v_rings_3204_);
lean_dec_ref(v_goal_3202_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object* v_goal_3214_, lean_object* v_config_3215_, lean_object* v_rings_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
uint8_t v_verbose_3222_; lean_object* v_mvarId_3223_; uint8_t v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___y_3227_; lean_object* v___x_3228_; 
v_verbose_3222_ = lean_ctor_get_uint8(v_config_3215_, sizeof(void*)*17 + 15);
v_mvarId_3223_ = lean_ctor_get(v_goal_3214_, 1);
lean_inc_n(v_mvarId_3223_, 2);
v___x_3224_ = 1;
v___x_3225_ = lean_box(v_verbose_3222_);
v___x_3226_ = lean_box(v___x_3224_);
v___y_3227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_goalToMessageData___lam__0___boxed), 11, 6);
lean_closure_set(v___y_3227_, 0, v___x_3225_);
lean_closure_set(v___y_3227_, 1, v_mvarId_3223_);
lean_closure_set(v___y_3227_, 2, v_goal_3214_);
lean_closure_set(v___y_3227_, 3, v_config_3215_);
lean_closure_set(v___y_3227_, 4, v_rings_3216_);
lean_closure_set(v___y_3227_, 5, v___x_3226_);
v___x_3228_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_goalToMessageData_spec__1___redArg(v_mvarId_3223_, v___y_3227_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_goalToMessageData___boxed(lean_object* v_goal_3229_, lean_object* v_config_3230_, lean_object* v_rings_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_Meta_Grind_goalToMessageData(v_goal_3229_, v_config_3230_, v_rings_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
return v_res_3237_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
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
lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
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
