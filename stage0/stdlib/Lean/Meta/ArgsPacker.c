// Lean compiler output
// Module: Lean.Meta.ArgsPacker
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.PProdN public import Lean.Meta.ArgsPacker.Basic import Init.Omega import Init.While
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Meta_PProdN_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_Unary_packType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_packType___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_packType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_packType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Unary_packType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_packType___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_packType___closed__1_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_Unary_packType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_packType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_packType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Meta.ArgsPacker"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Meta.ArgsPacker.0.Lean.Meta.ArgsPacker.Unary.pack.go"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "assertion violation: type.isAppOfArity ``PSigma 2\n      "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3;
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 38, .m_data = "assertion violation: β.isLambda\n      "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5;
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 249, 30, 71, 49, 108, 60, 175)}};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_Unary_pack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_pack___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_pack___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_pack___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Unary_packType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_pack___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_ArgsPacker_Unary_pack___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_ArgsPacker_Unary_pack___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_pack___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_pack___closed__1_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_Unary_pack___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_pack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_pack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0_value)}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.ArgsPacker.Unary.uncurryType"};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: xs.size = varNames.size\n      "};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2;
static const lean_string_object l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "ArgsPacker.Binary.casesOn: Expected PSigma type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 3, 119, 45, 252, 168, 83)}};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.ArgsPacker.Unary.uncurry"};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0_value;
static const lean_string_object l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__1_value;
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "curryType: Expected PSigma type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "curryType: Expected forall type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "curryPSigma: Expected PSigma type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "curryPSigma: expected forall type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Mutual.unpackType: Expected PSum type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: args.size == 2\n        "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Meta.ArgsPacker.0.Lean.Meta.ArgsPacker.Mutual.pack.go"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(201, 156, 94, 164, 220, 114, 107, 70)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__5_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(14, 217, 178, 28, 107, 212, 157, 131)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "assertion violation: xType.isAppOfArity ``PSum 2\n      "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Meta.ArgsPacker.0.Lean.Meta.ArgsPacker.Mutual.mkCodomain.go"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Mutual.uncurryType: Expected forall type, got "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Mutual.uncurryTypeND: Expected equal codomains, but got "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Mutual.uncurryTypeND: Expected non-dependent types, got "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Mutual.casesOn: no alternatives"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1;
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Mutual.casesOn: Expected PSum type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Meta.ArgsPacker.Mutual.uncurryWithType"};
static const lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Meta.ArgsPacker.Mutual.uncurryND"};
static const lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object*);
static lean_once_cell_t l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_pack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.ArgsPacker.pack"};
static const lean_object* l_Lean_Meta_ArgsPacker_pack___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_pack___closed__0_value;
static const lean_string_object l_Lean_Meta_ArgsPacker_pack___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "assertion violation: fidx < argsPacker.numFuncs\n  "};
static const lean_object* l_Lean_Meta_ArgsPacker_pack___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_pack___closed__1_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_pack___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_pack___closed__2;
static const lean_string_object l_Lean_Meta_ArgsPacker_pack___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "assertion violation: args.size == argsPacker.varNamess[fidx]!.size\n  "};
static const lean_object* l_Lean_Meta_ArgsPacker_pack___closed__3 = (const lean_object*)&l_Lean_Meta_ArgsPacker_pack___closed__3_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_pack___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_pack___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_curryProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "curryProj: index out of range"};
static const lean_object* l_Lean_Meta_ArgsPacker_curryProj___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_curryProj___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_curryProj___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_curryProj___closed__1;
static const lean_string_object l_Lean_Meta_ArgsPacker_curryProj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.ArgsPacker.curryProj"};
static const lean_object* l_Lean_Meta_ArgsPacker_curryProj___closed__2 = (const lean_object*)&l_Lean_Meta_ArgsPacker_curryProj___closed__2_value;
static const lean_string_object l_Lean_Meta_ArgsPacker_curryProj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "curryProj: expected forall type, got {}"};
static const lean_object* l_Lean_Meta_ArgsPacker_curryProj___closed__3 = (const lean_object*)&l_Lean_Meta_ArgsPacker_curryProj___closed__3_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_curryProj___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_curryProj___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_ArgsPacker_curry___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_curry___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "curryParam: unexpected packed motive, not a forall"};
static const lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1;
static const lean_string_object l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "curryParam: expected forall, got "};
static const lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(lean_object* v___x_4_, lean_object* v_as_5_, size_t v_sz_6_, size_t v_i_7_, lean_object* v_b_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_usize_dec_lt(v_i_7_, v_sz_6_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v_b_8_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_16_ = lean_array_uget_borrowed(v_as_5_, v_i_7_);
lean_inc(v___y_12_);
lean_inc_ref(v___y_11_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v_a_16_);
v___x_17_ = lean_infer_type(v_a_16_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_50_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_50_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_50_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_50_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; uint8_t v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_nat_dec_eq(v___x_4_, v___x_22_);
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_mk_empty_array_with_capacity(v___x_24_);
lean_inc(v_a_16_);
v___x_26_ = lean_array_push(v___x_25_, v_a_16_);
v___x_27_ = 1;
v___x_28_ = l_Lean_Meta_mkLambdaFVars(v___x_26_, v_b_8_, v___x_23_, v___x_14_, v___x_23_, v___x_14_, v___x_27_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
lean_dec_ref(v___x_26_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_49_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_49_ == 0)
{
v___x_31_ = v___x_28_;
v_isShared_32_ = v_isSharedCheck_49_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_49_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 1);
lean_ctor_set(v___x_31_, 0, v_a_18_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_18_);
v___x_35_ = v_reuseFailAlloc_48_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 1);
lean_ctor_set(v___x_20_, 0, v_a_29_);
v___x_37_ = v___x_20_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_29_);
v___x_37_ = v_reuseFailAlloc_47_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_38_ = lean_unsigned_to_nat(2u);
v___x_39_ = lean_mk_empty_array_with_capacity(v___x_38_);
v___x_40_ = lean_array_push(v___x_39_, v___x_35_);
v___x_41_ = lean_array_push(v___x_40_, v___x_37_);
v___x_42_ = l_Lean_Meta_mkAppOptM(v___x_33_, v___x_41_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; size_t v___x_44_; size_t v___x_45_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_42_, 1);
v___x_44_ = ((size_t)1ULL);
v___x_45_ = lean_usize_add(v_i_7_, v___x_44_);
v_i_7_ = v___x_45_;
v_b_8_ = v_a_43_;
goto _start;
}
else
{
return v___x_42_;
}
}
}
}
}
else
{
lean_del_object(v___x_20_);
lean_dec(v_a_18_);
return v___x_28_;
}
}
}
else
{
lean_dec_ref(v_b_8_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___boxed(lean_object* v___x_51_, lean_object* v_as_52_, lean_object* v_sz_53_, lean_object* v_i_54_, lean_object* v_b_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
size_t v_sz_boxed_61_; size_t v_i_boxed_62_; lean_object* v_res_63_; 
v_sz_boxed_61_ = lean_unbox_usize(v_sz_53_);
lean_dec(v_sz_53_);
v_i_boxed_62_ = lean_unbox_usize(v_i_54_);
lean_dec(v_i_54_);
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(v___x_51_, v_as_52_, v_sz_boxed_61_, v_i_boxed_62_, v_b_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec_ref(v_as_52_);
lean_dec(v___x_51_);
return v_res_63_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1));
v___x_69_ = l_Lean_mkConst(v___x_68_, v___x_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_packType(lean_object* v_xs_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_76_ = lean_array_get_size(v_xs_70_);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_nat_dec_eq(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = l_Lean_instInhabitedExpr;
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_sub(v___x_76_, v___x_80_);
v___x_82_ = lean_array_get_borrowed(v___x_79_, v_xs_70_, v___x_81_);
lean_dec(v___x_81_);
lean_inc(v_a_74_);
lean_inc_ref(v_a_73_);
lean_inc(v_a_72_);
lean_inc_ref(v_a_71_);
lean_inc(v___x_82_);
v___x_83_ = lean_infer_type(v___x_82_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_85_; lean_object* v___x_86_; size_t v_sz_87_; size_t v___x_88_; lean_object* v___x_89_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_84_);
lean_dec_ref_known(v___x_83_, 1);
v___x_85_ = lean_array_pop(v_xs_70_);
v___x_86_ = l_Array_reverse___redArg(v___x_85_);
v_sz_87_ = lean_array_size(v___x_86_);
v___x_88_ = ((size_t)0ULL);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(v___x_76_, v___x_86_, v_sz_87_, v___x_88_, v_a_84_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
lean_dec_ref(v___x_86_);
return v___x_89_;
}
else
{
lean_dec_ref(v_xs_70_);
return v___x_83_;
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec_ref(v_xs_70_);
v___x_90_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_packType___boxed(lean_object* v_xs_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Meta_ArgsPacker_Unary_packType(v_xs_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(lean_object* v_msg_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = l_Lean_instInhabitedExpr;
v___x_101_ = lean_panic_fn_borrowed(v___x_100_, v_msg_99_);
return v___x_101_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_105_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2));
v___x_106_ = lean_unsigned_to_nat(6u);
v___x_107_ = lean_unsigned_to_nat(86u);
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1));
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_110_ = l_mkPanicMessageWithDecl(v___x_109_, v___x_108_, v___x_107_, v___x_106_, v___x_105_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4));
v___x_113_ = lean_unsigned_to_nat(6u);
v___x_114_ = lean_unsigned_to_nat(90u);
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1));
v___x_116_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_117_ = l_mkPanicMessageWithDecl(v___x_116_, v___x_115_, v___x_114_, v___x_113_, v___x_112_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(lean_object* v_args_122_, lean_object* v_i_123_, lean_object* v_type_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_125_ = lean_array_get_size(v_args_122_);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_sub(v___x_125_, v___x_126_);
v___x_128_ = lean_nat_dec_lt(v_i_123_, v___x_127_);
lean_dec(v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = l_Lean_instInhabitedExpr;
v___x_130_ = lean_array_get_borrowed(v___x_129_, v_args_122_, v_i_123_);
lean_inc(v___x_130_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_132_ = lean_unsigned_to_nat(2u);
v___x_133_ = l_Lean_Expr_isAppOfArity(v_type_124_, v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3);
v___x_135_ = l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(v___x_134_);
return v___x_135_;
}
else
{
lean_object* v_00_u03b2_136_; uint8_t v___x_137_; 
v_00_u03b2_136_ = l_Lean_Expr_appArg_x21(v_type_124_);
v___x_137_ = l_Lean_Expr_isLambda(v_00_u03b2_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec_ref(v_00_u03b2_136_);
v___x_138_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5);
v___x_139_ = l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(v___x_138_);
return v___x_139_;
}
else
{
lean_object* v_arg_140_; lean_object* v___x_141_; lean_object* v_us_142_; lean_object* v___x_143_; lean_object* v_00_u03b1_144_; lean_object* v___x_145_; lean_object* v_type_146_; lean_object* v___x_147_; lean_object* v_rest_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_arg_140_ = lean_array_fget_borrowed(v_args_122_, v_i_123_);
v___x_141_ = l_Lean_Expr_getAppFn(v_type_124_);
v_us_142_ = l_Lean_Expr_constLevels_x21(v___x_141_);
lean_dec_ref(v___x_141_);
v___x_143_ = l_Lean_Expr_appFn_x21(v_type_124_);
v_00_u03b1_144_ = l_Lean_Expr_appArg_x21(v___x_143_);
lean_dec_ref(v___x_143_);
v___x_145_ = l_Lean_Expr_bindingBody_x21(v_00_u03b2_136_);
v_type_146_ = lean_expr_instantiate1(v___x_145_, v_arg_140_);
lean_dec_ref(v___x_145_);
v___x_147_ = lean_nat_add(v_i_123_, v___x_126_);
v_rest_148_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(v_args_122_, v___x_147_, v_type_146_);
lean_dec_ref(v_type_146_);
lean_dec(v___x_147_);
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7));
v___x_150_ = l_Lean_mkConst(v___x_149_, v_us_142_);
lean_inc(v_arg_140_);
v___x_151_ = l_Lean_mkApp4(v___x_150_, v_00_u03b1_144_, v_00_u03b2_136_, v_arg_140_, v_rest_148_);
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___boxed(lean_object* v_args_152_, lean_object* v_i_153_, lean_object* v_type_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(v_args_152_, v_i_153_, v_type_154_);
lean_dec_ref(v_type_154_);
lean_dec(v_i_153_);
lean_dec_ref(v_args_152_);
return v_res_155_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_box(0);
v___x_161_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_pack___closed__1));
v___x_162_ = l_Lean_mkConst(v___x_161_, v___x_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_pack(lean_object* v_type_163_, lean_object* v_args_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_165_ = lean_array_get_size(v_args_164_);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_nat_dec_eq(v___x_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(v_args_164_, v___x_166_, v_type_163_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_pack___closed__2, &l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_pack___boxed(lean_object* v_type_170_, lean_object* v_args_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_type_170_, v_args_171_);
lean_dec_ref(v_args_171_);
lean_dec_ref(v_type_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(lean_object* v_upperBound_173_, lean_object* v_a_174_, lean_object* v_b_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = lean_nat_dec_lt(v_a_174_, v_upperBound_173_);
if (v___x_176_ == 0)
{
lean_dec(v_a_174_);
return v_b_175_;
}
else
{
lean_object* v_fst_177_; lean_object* v_snd_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_193_; 
v_fst_177_ = lean_ctor_get(v_b_175_, 0);
v_snd_178_ = lean_ctor_get(v_b_175_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_b_175_);
if (v_isSharedCheck_193_ == 0)
{
v___x_180_ = v_b_175_;
v_isShared_181_ = v_isSharedCheck_193_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_snd_178_);
lean_inc(v_fst_177_);
lean_dec(v_b_175_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_193_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
lean_inc(v_snd_178_);
v___x_185_ = l_Lean_mkProj(v___x_184_, v___x_182_, v_snd_178_);
v___x_186_ = lean_array_push(v_fst_177_, v___x_185_);
v___x_187_ = l_Lean_mkProj(v___x_184_, v___x_183_, v_snd_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_187_);
lean_ctor_set(v___x_180_, 0, v___x_186_);
v___x_189_ = v___x_180_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_187_);
v___x_189_ = v_reuseFailAlloc_192_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; 
v___x_190_ = lean_nat_add(v_a_174_, v___x_183_);
lean_dec(v_a_174_);
v_a_174_ = v___x_190_;
v_b_175_ = v___x_189_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg___boxed(lean_object* v_upperBound_194_, lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_194_, v_a_195_, v_b_196_);
lean_dec(v_upperBound_194_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(lean_object* v_t_200_, lean_object* v_arity_201_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_nat_dec_eq(v_arity_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_result_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_211_; 
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_sub(v_arity_201_, v___x_204_);
v_result_206_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v_result_206_);
lean_ctor_set(v___x_207_, 1, v_t_200_);
v___x_208_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v___x_205_, v___x_202_, v___x_207_);
lean_dec(v___x_205_);
v_fst_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_fst_209_);
v_snd_210_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_snd_210_);
lean_dec_ref(v___x_208_);
v___x_211_ = lean_array_push(v_fst_209_, v_snd_210_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; 
lean_dec_ref(v_t_200_);
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___boxed(lean_object* v_t_213_, lean_object* v_arity_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_t_213_, v_arity_214_);
lean_dec(v_arity_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(lean_object* v_upperBound_216_, lean_object* v_inst_217_, lean_object* v_R_218_, lean_object* v_a_219_, lean_object* v_b_220_, lean_object* v_c_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_216_, v_a_219_, v_b_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___boxed(lean_object* v_upperBound_223_, lean_object* v_inst_224_, lean_object* v_R_225_, lean_object* v_a_226_, lean_object* v_b_227_, lean_object* v_c_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(v_upperBound_223_, v_inst_224_, v_R_225_, v_a_226_, v_b_227_, v_c_228_);
lean_dec(v_upperBound_223_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(lean_object* v_arity_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_snd_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_285_; 
v_snd_232_ = lean_ctor_get(v_a_231_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_a_231_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v_a_231_, 0);
lean_dec(v_unused_286_);
v___x_234_ = v_a_231_;
v_isShared_235_ = v_isSharedCheck_285_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_snd_232_);
lean_dec(v_a_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_285_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_284_; 
v_fst_236_ = lean_ctor_get(v_snd_232_, 0);
v_snd_237_ = lean_ctor_get(v_snd_232_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_snd_232_);
if (v_isSharedCheck_284_ == 0)
{
v___x_239_ = v_snd_232_;
v_isShared_240_ = v_isSharedCheck_284_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_snd_237_);
lean_inc(v_fst_236_);
lean_dec(v_snd_232_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_284_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_241_ = lean_box(0);
v___x_242_ = lean_array_get_size(v_snd_237_);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v___x_242_, v___x_243_);
v___x_245_ = lean_nat_dec_lt(v___x_244_, v_arity_230_);
lean_dec(v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_247_; 
if (v_isShared_240_ == 0)
{
v___x_247_ = v___x_239_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_fst_236_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_snd_237_);
v___x_247_ = v_reuseFailAlloc_252_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_249_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_247_);
lean_ctor_set(v___x_234_, 0, v___x_241_);
v___x_249_ = v___x_234_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_251_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7));
v___x_254_ = lean_unsigned_to_nat(4u);
v___x_255_ = l_Lean_Expr_isAppOfArity(v_fst_236_, v___x_253_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_256_ = lean_nat_sub(v_arity_230_, v___x_242_);
lean_inc(v_fst_236_);
v___x_257_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_fst_236_, v___x_256_);
lean_dec(v___x_256_);
lean_inc(v_snd_237_);
v___x_258_ = l_Array_append___redArg(v_snd_237_, v___x_257_);
lean_dec_ref(v___x_257_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
if (v_isShared_240_ == 0)
{
v___x_261_ = v___x_239_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_236_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_snd_237_);
v___x_261_ = v_reuseFailAlloc_266_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_261_);
lean_ctor_set(v___x_234_, 0, v___x_259_);
v___x_263_ = v___x_234_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_267_ = lean_unsigned_to_nat(2u);
v___x_268_ = l_Lean_Expr_getAppNumArgs(v_fst_236_);
v___x_269_ = lean_nat_sub(v___x_268_, v___x_267_);
v___x_270_ = lean_nat_sub(v___x_269_, v___x_243_);
lean_dec(v___x_269_);
v___x_271_ = l_Lean_Expr_getRevArg_x21(v_fst_236_, v___x_270_);
v___x_272_ = lean_array_push(v_snd_237_, v___x_271_);
v___x_273_ = lean_unsigned_to_nat(3u);
v___x_274_ = lean_nat_sub(v___x_268_, v___x_273_);
lean_dec(v___x_268_);
v___x_275_ = lean_nat_sub(v___x_274_, v___x_243_);
lean_dec(v___x_274_);
v___x_276_ = l_Lean_Expr_getRevArg_x21(v_fst_236_, v___x_275_);
lean_dec(v_fst_236_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_272_);
lean_ctor_set(v___x_239_, 0, v___x_276_);
v___x_278_ = v___x_239_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_272_);
v___x_278_ = v_reuseFailAlloc_283_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_278_);
lean_ctor_set(v___x_234_, 0, v___x_241_);
v___x_280_ = v___x_234_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_282_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
v_a_231_ = v___x_280_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg___boxed(lean_object* v_arity_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_287_, v_a_288_);
lean_dec(v_arity_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack(lean_object* v_arity_292_, lean_object* v_e_293_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_nat_dec_eq(v_arity_292_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v_args_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_args_296_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_e_293_);
lean_ctor_set(v___x_298_, 1, v_args_296_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_292_, v___x_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
return v___x_297_;
}
else
{
lean_object* v_val_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_313_; 
v_val_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_313_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_val_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_fst_305_; 
v_fst_305_ = lean_ctor_get(v_val_301_, 0);
if (lean_obj_tag(v_fst_305_) == 0)
{
lean_object* v_snd_306_; lean_object* v_fst_307_; lean_object* v_snd_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v_snd_306_ = lean_ctor_get(v_val_301_, 1);
lean_inc(v_snd_306_);
lean_dec(v_val_301_);
v_fst_307_ = lean_ctor_get(v_snd_306_, 0);
lean_inc(v_fst_307_);
v_snd_308_ = lean_ctor_get(v_snd_306_, 1);
lean_inc(v_snd_308_);
lean_dec(v_snd_306_);
v___x_309_ = lean_array_push(v_snd_308_, v_fst_307_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_309_);
v___x_311_ = v___x_303_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
else
{
lean_inc_ref(v_fst_305_);
lean_del_object(v___x_303_);
lean_dec(v_val_301_);
return v_fst_305_;
}
}
}
}
else
{
lean_object* v___x_314_; 
lean_dec_ref(v_e_293_);
v___x_314_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___boxed(lean_object* v_arity_315_, lean_object* v_e_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v_arity_315_, v_e_316_);
lean_dec(v_arity_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(lean_object* v_arity_318_, lean_object* v_inst_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_318_, v_a_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___boxed(lean_object* v_arity_322_, lean_object* v_inst_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(v_arity_322_, v_inst_323_, v_a_324_);
lean_dec(v_arity_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___f_333_; lean_object* v___x_450__overap_334_; lean_object* v___x_335_; 
v___f_333_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_450__overap_334_ = lean_panic_fn_borrowed(v___f_333_, v_msg_327_);
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
v___x_335_ = lean_apply_5(v___x_450__overap_334_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, lean_box(0));
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___boxed(lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(lean_object* v_k_343_, lean_object* v_b_344_, lean_object* v_c_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
lean_inc(v___y_349_);
lean_inc_ref(v___y_348_);
lean_inc(v___y_347_);
lean_inc_ref(v___y_346_);
v___x_351_ = lean_apply_7(v_k_343_, v_b_344_, v_c_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, lean_box(0));
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed(lean_object* v_k_352_, lean_object* v_b_353_, lean_object* v_c_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(v_k_352_, v_b_353_, v_c_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(lean_object* v_type_361_, lean_object* v_maxFVars_x3f_362_, lean_object* v_k_363_, uint8_t v_cleanupAnnotations_364_, uint8_t v_whnfType_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___f_371_; lean_object* v___x_372_; 
v___f_371_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_371_, 0, v_k_363_);
v___x_372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_361_, v_maxFVars_x3f_362_, v___f_371_, v_cleanupAnnotations_364_, v_whnfType_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_a_381_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_372_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_372_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___boxed(lean_object* v_type_389_, lean_object* v_maxFVars_x3f_390_, lean_object* v_k_391_, lean_object* v_cleanupAnnotations_392_, lean_object* v_whnfType_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_399_; uint8_t v_whnfType_boxed_400_; lean_object* v_res_401_; 
v_cleanupAnnotations_boxed_399_ = lean_unbox(v_cleanupAnnotations_392_);
v_whnfType_boxed_400_ = lean_unbox(v_whnfType_393_);
v_res_401_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_389_, v_maxFVars_x3f_390_, v_k_391_, v_cleanupAnnotations_boxed_399_, v_whnfType_boxed_400_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(lean_object* v_00_u03b1_402_, lean_object* v_type_403_, lean_object* v_maxFVars_x3f_404_, lean_object* v_k_405_, uint8_t v_cleanupAnnotations_406_, uint8_t v_whnfType_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_403_, v_maxFVars_x3f_404_, v_k_405_, v_cleanupAnnotations_406_, v_whnfType_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___boxed(lean_object* v_00_u03b1_414_, lean_object* v_type_415_, lean_object* v_maxFVars_x3f_416_, lean_object* v_k_417_, lean_object* v_cleanupAnnotations_418_, lean_object* v_whnfType_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_425_; uint8_t v_whnfType_boxed_426_; lean_object* v_res_427_; 
v_cleanupAnnotations_boxed_425_ = lean_unbox(v_cleanupAnnotations_418_);
v_whnfType_boxed_426_ = lean_unbox(v_whnfType_419_);
v_res_427_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(v_00_u03b1_414_, v_type_415_, v_maxFVars_x3f_416_, v_k_417_, v_cleanupAnnotations_boxed_425_, v_whnfType_boxed_426_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(lean_object* v___x_428_, lean_object* v_type_429_, uint8_t v___x_430_, uint8_t v___x_431_, lean_object* v_tuple_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_inc_ref(v_tuple_432_);
v___x_438_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_tuple_432_, v___x_428_);
v___x_439_ = l_Lean_Meta_instantiateForall(v_type_429_, v___x_438_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec_ref(v___x_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_mk_empty_array_with_capacity(v___x_441_);
v___x_443_ = lean_array_push(v___x_442_, v_tuple_432_);
v___x_444_ = 1;
v___x_445_ = l_Lean_Meta_mkForallFVars(v___x_443_, v_a_440_, v___x_430_, v___x_431_, v___x_431_, v___x_444_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec_ref(v___x_443_);
return v___x_445_;
}
else
{
lean_dec_ref(v_tuple_432_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed(lean_object* v___x_446_, lean_object* v_type_447_, lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v_tuple_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
uint8_t v___x_1259__boxed_456_; uint8_t v___x_1260__boxed_457_; lean_object* v_res_458_; 
v___x_1259__boxed_456_ = lean_unbox(v___x_448_);
v___x_1260__boxed_457_ = lean_unbox(v___x_449_);
v_res_458_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(v___x_446_, v_type_447_, v___x_1259__boxed_456_, v___x_1260__boxed_457_, v_tuple_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___x_446_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(lean_object* v_k_459_, lean_object* v_b_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; 
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
v___x_466_ = lean_apply_6(v_k_459_, v_b_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, lean_box(0));
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_467_, lean_object* v_b_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(v_k_467_, v_b_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(lean_object* v_name_475_, uint8_t v_bi_476_, lean_object* v_type_477_, lean_object* v_k_478_, uint8_t v_kind_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___f_485_; lean_object* v___x_486_; 
v___f_485_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_485_, 0, v_k_478_);
v___x_486_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_475_, v_bi_476_, v_type_477_, v___f_485_, v_kind_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_486_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_486_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___boxed(lean_object* v_name_503_, lean_object* v_bi_504_, lean_object* v_type_505_, lean_object* v_k_506_, lean_object* v_kind_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v_bi_boxed_513_; uint8_t v_kind_boxed_514_; lean_object* v_res_515_; 
v_bi_boxed_513_ = lean_unbox(v_bi_504_);
v_kind_boxed_514_ = lean_unbox(v_kind_507_);
v_res_515_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_503_, v_bi_boxed_513_, v_type_505_, v_k_506_, v_kind_boxed_514_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(lean_object* v_name_516_, lean_object* v_type_517_, lean_object* v_k_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; 
v___x_524_ = 0;
v___x_525_ = 0;
v___x_526_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_516_, v___x_524_, v_type_517_, v_k_518_, v___x_525_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg___boxed(lean_object* v_name_527_, lean_object* v_type_528_, lean_object* v_k_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_527_, v_type_528_, v_k_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_535_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_538_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1));
v___x_539_ = lean_unsigned_to_nat(6u);
v___x_540_ = lean_unsigned_to_nat(141u);
v___x_541_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0));
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_543_ = l_mkPanicMessageWithDecl(v___x_542_, v___x_541_, v___x_540_, v___x_539_, v___x_538_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(lean_object* v___x_547_, lean_object* v_type_548_, uint8_t v___x_549_, uint8_t v___x_550_, lean_object* v___x_551_, lean_object* v_varNames_552_, lean_object* v___x_553_, lean_object* v_xs_554_, lean_object* v_x_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_array_get_size(v_xs_554_);
v___x_562_ = lean_nat_dec_eq(v___x_561_, v___x_547_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_xs_554_);
lean_dec_ref(v_type_548_);
v___x_563_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2);
v___x_564_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_563_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Meta_ArgsPacker_Unary_packType(v_xs_554_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___f_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = lean_box(v___x_549_);
v___x_568_ = lean_box(v___x_550_);
v___f_569_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_569_, 0, v___x_561_);
lean_closure_set(v___f_569_, 1, v_type_548_);
lean_closure_set(v___f_569_, 2, v___x_567_);
lean_closure_set(v___f_569_, 3, v___x_568_);
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_dec_eq(v___x_561_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_573_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_572_, v_a_566_, v___f_569_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_array_get_borrowed(v___x_551_, v_varNames_552_, v___x_553_);
lean_inc(v___x_574_);
v___x_575_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_574_, v_a_566_, v___f_569_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
return v___x_575_;
}
}
else
{
lean_dec_ref(v_type_548_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed(lean_object* v___x_576_, lean_object* v_type_577_, lean_object* v___x_578_, lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v_varNames_581_, lean_object* v___x_582_, lean_object* v_xs_583_, lean_object* v_x_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___x_1412__boxed_590_; uint8_t v___x_1413__boxed_591_; lean_object* v_res_592_; 
v___x_1412__boxed_590_ = lean_unbox(v___x_578_);
v___x_1413__boxed_591_ = lean_unbox(v___x_579_);
v_res_592_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(v___x_576_, v_type_577_, v___x_1412__boxed_590_, v___x_1413__boxed_591_, v___x_580_, v_varNames_581_, v___x_582_, v_xs_583_, v_x_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec_ref(v_x_584_);
lean_dec(v___x_582_);
lean_dec_ref(v_varNames_581_);
lean_dec(v___x_580_);
lean_dec(v___x_576_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType(lean_object* v_varNames_593_, lean_object* v_type_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = lean_array_get_size(v_varNames_593_);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_nat_dec_eq(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_603_ = lean_box(0);
v___x_604_ = 1;
v___x_605_ = lean_box(v___x_602_);
v___x_606_ = lean_box(v___x_604_);
lean_inc_ref(v_type_594_);
v___f_607_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed), 14, 7);
lean_closure_set(v___f_607_, 0, v___x_600_);
lean_closure_set(v___f_607_, 1, v_type_594_);
lean_closure_set(v___f_607_, 2, v___x_605_);
lean_closure_set(v___f_607_, 3, v___x_606_);
lean_closure_set(v___f_607_, 4, v___x_603_);
lean_closure_set(v___f_607_, 5, v_varNames_593_);
lean_closure_set(v___f_607_, 6, v___x_601_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_600_);
v___x_609_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_594_, v___x_608_, v___f_607_, v___x_602_, v___x_602_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec_ref(v_varNames_593_);
v___x_610_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_611_ = l_Lean_mkArrow(v___x_610_, v_type_594_, v_a_597_, v_a_598_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___boxed(lean_object* v_varNames_612_, lean_object* v_type_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_612_, v_type_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(lean_object* v_00_u03b1_620_, lean_object* v_name_621_, uint8_t v_bi_622_, lean_object* v_type_623_, lean_object* v_k_624_, uint8_t v_kind_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_621_, v_bi_622_, v_type_623_, v_k_624_, v_kind_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_632_, lean_object* v_name_633_, lean_object* v_bi_634_, lean_object* v_type_635_, lean_object* v_k_636_, lean_object* v_kind_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
uint8_t v_bi_boxed_643_; uint8_t v_kind_boxed_644_; lean_object* v_res_645_; 
v_bi_boxed_643_ = lean_unbox(v_bi_634_);
v_kind_boxed_644_ = lean_unbox(v_kind_637_);
v_res_645_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(v_00_u03b1_632_, v_name_633_, v_bi_boxed_643_, v_type_635_, v_k_636_, v_kind_boxed_644_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(lean_object* v_00_u03b1_646_, lean_object* v_name_647_, lean_object* v_type_648_, lean_object* v_k_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_647_, v_type_648_, v_k_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___boxed(lean_object* v_00_u03b1_656_, lean_object* v_name_657_, lean_object* v_type_658_, lean_object* v_k_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(v_00_u03b1_656_, v_name_657_, v_type_658_, v_k_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(lean_object* v_msgData_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v_env_673_; lean_object* v___x_674_; lean_object* v_mctx_675_; lean_object* v_lctx_676_; lean_object* v_options_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_672_ = lean_st_ref_get(v___y_670_);
v_env_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_env_673_);
lean_dec(v___x_672_);
v___x_674_ = lean_st_ref_get(v___y_668_);
v_mctx_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc_ref(v_mctx_675_);
lean_dec(v___x_674_);
v_lctx_676_ = lean_ctor_get(v___y_667_, 2);
v_options_677_ = lean_ctor_get(v___y_669_, 2);
lean_inc_ref(v_options_677_);
lean_inc_ref(v_lctx_676_);
v___x_678_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_678_, 0, v_env_673_);
lean_ctor_set(v___x_678_, 1, v_mctx_675_);
lean_ctor_set(v___x_678_, 2, v_lctx_676_);
lean_ctor_set(v___x_678_, 3, v_options_677_);
v___x_679_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v_msgData_666_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0___boxed(lean_object* v_msgData_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msgData_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(lean_object* v_msg_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_ref_694_; lean_object* v___x_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_ref_694_ = lean_ctor_get(v___y_691_, 5);
v___x_695_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msg_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_inc(v_ref_694_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_ref_694_);
lean_ctor_set(v___x_700_, 1, v_a_696_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg___boxed(lean_object* v_msg_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0));
v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed(lean_object** _args){
lean_object* v___x_715_ = _args[0];
lean_object* v___x_716_ = _args[1];
lean_object* v___x_717_ = _args[2];
lean_object* v_arg_718_ = _args[3];
lean_object* v_arg_719_ = _args[4];
lean_object* v_a_720_ = _args[5];
lean_object* v_alt_721_ = _args[6];
lean_object* v_tail_722_ = _args[7];
lean_object* v_u_723_ = _args[8];
lean_object* v___x_724_ = _args[9];
lean_object* v___x_725_ = _args[10];
lean_object* v___x_726_ = _args[11];
lean_object* v_head_727_ = _args[12];
lean_object* v_x_728_ = _args[13];
lean_object* v___y_729_ = _args[14];
lean_object* v___y_730_ = _args[15];
lean_object* v___y_731_ = _args[16];
lean_object* v___y_732_ = _args[17];
lean_object* v___y_733_ = _args[18];
_start:
{
uint8_t v___x_2928__boxed_734_; uint8_t v___x_2929__boxed_735_; uint8_t v___x_2930__boxed_736_; lean_object* v_res_737_; 
v___x_2928__boxed_734_ = lean_unbox(v___x_724_);
v___x_2929__boxed_735_ = lean_unbox(v___x_725_);
v___x_2930__boxed_736_ = lean_unbox(v___x_726_);
v_res_737_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(v___x_715_, v___x_716_, v___x_717_, v_arg_718_, v_arg_719_, v_a_720_, v_alt_721_, v_tail_722_, v_u_723_, v___x_2928__boxed_734_, v___x_2929__boxed_735_, v___x_2930__boxed_736_, v_head_727_, v_x_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(lean_object* v_varNames_742_, lean_object* v_e_743_, lean_object* v_u_744_, lean_object* v_codomain_745_, lean_object* v_alt_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
if (lean_obj_tag(v_varNames_742_) == 0)
{
lean_object* v___x_752_; 
lean_dec_ref(v_codomain_745_);
lean_dec(v_u_744_);
lean_dec_ref(v_e_743_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v_alt_746_);
return v___x_752_;
}
else
{
lean_object* v_tail_753_; 
v_tail_753_ = lean_ctor_get(v_varNames_742_, 1);
lean_inc(v_tail_753_);
if (lean_obj_tag(v_tail_753_) == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref_known(v_varNames_742_, 2);
lean_dec_ref(v_codomain_745_);
lean_dec(v_u_744_);
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_mk_empty_array_with_capacity(v___x_754_);
v___x_756_ = lean_array_push(v___x_755_, v_e_743_);
v___x_757_ = l_Lean_Expr_beta(v_alt_746_, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
else
{
lean_object* v_head_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_815_; 
v_head_759_ = lean_ctor_get(v_varNames_742_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v_varNames_742_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v_varNames_742_, 1);
lean_dec(v_unused_816_);
v___x_761_ = v_varNames_742_;
v_isShared_762_ = v_isSharedCheck_815_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_head_759_);
lean_dec(v_varNames_742_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_815_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_head_763_; lean_object* v___x_764_; 
v_head_763_ = lean_ctor_get(v_tail_753_, 0);
lean_inc(v_head_763_);
lean_inc(v_a_750_);
lean_inc_ref(v_a_749_);
lean_inc(v_a_748_);
lean_inc_ref(v_a_747_);
lean_inc_ref(v_e_743_);
v___x_764_ = lean_infer_type(v_e_743_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_n(v_a_765_, 2);
lean_dec_ref_known(v___x_764_, 1);
v___x_766_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_765_, v_a_748_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_777_ = l_Lean_Expr_cleanupAnnotations(v_a_767_);
v___x_778_ = l_Lean_Expr_isApp(v___x_777_);
if (v___x_778_ == 0)
{
lean_dec_ref(v___x_777_);
lean_dec(v_head_763_);
lean_del_object(v___x_761_);
lean_dec(v_head_759_);
lean_dec_ref_known(v_tail_753_, 2);
lean_dec_ref(v_alt_746_);
lean_dec_ref(v_codomain_745_);
lean_dec(v_u_744_);
lean_dec_ref(v_e_743_);
v___y_769_ = v_a_747_;
v___y_770_ = v_a_748_;
v___y_771_ = v_a_749_;
v___y_772_ = v_a_750_;
goto v___jp_768_;
}
else
{
lean_object* v_arg_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_arg_779_ = lean_ctor_get(v___x_777_, 1);
lean_inc_ref(v_arg_779_);
v___x_780_ = l_Lean_Expr_appFnCleanup___redArg(v___x_777_);
v___x_781_ = l_Lean_Expr_isApp(v___x_780_);
if (v___x_781_ == 0)
{
lean_dec_ref(v___x_780_);
lean_dec_ref(v_arg_779_);
lean_dec(v_head_763_);
lean_del_object(v___x_761_);
lean_dec_ref_known(v_tail_753_, 2);
lean_dec(v_head_759_);
lean_dec_ref(v_alt_746_);
lean_dec_ref(v_codomain_745_);
lean_dec(v_u_744_);
lean_dec_ref(v_e_743_);
v___y_769_ = v_a_747_;
v___y_770_ = v_a_748_;
v___y_771_ = v_a_749_;
v___y_772_ = v_a_750_;
goto v___jp_768_;
}
else
{
lean_object* v_arg_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_arg_782_ = lean_ctor_get(v___x_780_, 1);
lean_inc_ref(v_arg_782_);
v___x_783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_780_);
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0));
v___x_785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_786_ = l_Lean_Expr_isConstOf(v___x_783_, v___x_785_);
lean_dec_ref(v___x_783_);
if (v___x_786_ == 0)
{
lean_dec_ref(v_arg_782_);
lean_dec_ref(v_arg_779_);
lean_dec(v_head_763_);
lean_del_object(v___x_761_);
lean_dec(v_head_759_);
lean_dec_ref_known(v_tail_753_, 2);
lean_dec_ref(v_alt_746_);
lean_dec_ref(v_codomain_745_);
lean_dec(v_u_744_);
lean_dec_ref(v_e_743_);
v___y_769_ = v_a_747_;
v___y_770_ = v_a_748_;
v___y_771_ = v_a_749_;
v___y_772_ = v_a_750_;
goto v___jp_768_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_mk_empty_array_with_capacity(v___x_787_);
lean_inc_ref(v_e_743_);
lean_inc_ref(v___x_788_);
v___x_789_ = lean_array_push(v___x_788_, v_e_743_);
v___x_790_ = 0;
v___x_791_ = 1;
v___x_792_ = l_Lean_Meta_mkLambdaFVars(v___x_789_, v_codomain_745_, v___x_790_, v___x_786_, v___x_790_, v___x_786_, v___x_791_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec_ref(v___x_789_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___f_799_; lean_object* v___x_800_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc_n(v_a_793_, 2);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = l_Lean_Expr_getAppFn(v_a_765_);
lean_dec(v_a_765_);
v___x_795_ = l_Lean_Expr_constLevels_x21(v___x_794_);
lean_dec_ref(v___x_794_);
v___x_796_ = lean_box(v___x_790_);
v___x_797_ = lean_box(v___x_786_);
v___x_798_ = lean_box(v___x_791_);
lean_inc(v_u_744_);
lean_inc_ref(v_arg_779_);
lean_inc_ref_n(v_arg_782_, 2);
lean_inc(v___x_795_);
v___f_799_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed), 19, 13);
lean_closure_set(v___f_799_, 0, v___x_788_);
lean_closure_set(v___f_799_, 1, v___x_784_);
lean_closure_set(v___f_799_, 2, v___x_795_);
lean_closure_set(v___f_799_, 3, v_arg_782_);
lean_closure_set(v___f_799_, 4, v_arg_779_);
lean_closure_set(v___f_799_, 5, v_a_793_);
lean_closure_set(v___f_799_, 6, v_alt_746_);
lean_closure_set(v___f_799_, 7, v_tail_753_);
lean_closure_set(v___f_799_, 8, v_u_744_);
lean_closure_set(v___f_799_, 9, v___x_796_);
lean_closure_set(v___f_799_, 10, v___x_797_);
lean_closure_set(v___f_799_, 11, v___x_798_);
lean_closure_set(v___f_799_, 12, v_head_763_);
v___x_800_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_759_, v_arg_782_, v___f_799_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_814_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_814_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_814_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_814_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3));
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_795_);
lean_ctor_set(v___x_761_, 0, v_u_744_);
v___x_807_ = v___x_761_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_u_744_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_795_);
v___x_807_ = v_reuseFailAlloc_813_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = l_Lean_Expr_const___override(v___x_805_, v___x_807_);
v___x_809_ = l_Lean_mkApp5(v___x_808_, v_arg_782_, v_arg_779_, v_a_793_, v_e_743_, v_a_801_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_809_);
v___x_811_ = v___x_803_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_dec(v___x_795_);
lean_dec(v_a_793_);
lean_dec_ref(v_arg_782_);
lean_dec_ref(v_arg_779_);
lean_del_object(v___x_761_);
lean_dec(v_u_744_);
lean_dec_ref(v_e_743_);
return v___x_800_;
}
}
else
{
lean_dec_ref(v___x_788_);
lean_dec_ref(v_arg_782_);
lean_dec_ref(v_arg_779_);
lean_dec(v_a_765_);
lean_dec(v_head_763_);
lean_del_object(v___x_761_);
lean_dec(v_head_759_);
lean_dec_ref_known(v_tail_753_, 2);
lean_dec_ref(v_alt_746_);
lean_dec(v_u_744_);
lean_dec_ref(v_e_743_);
return v___x_792_;
}
}
}
}
v___jp_768_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1);
v___x_774_ = l_Lean_MessageData_ofExpr(v_a_765_);
v___x_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_775_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
return v___x_776_;
}
}
else
{
lean_dec(v_a_765_);
lean_dec(v_head_763_);
lean_del_object(v___x_761_);
lean_dec(v_head_759_);
lean_dec_ref_known(v_tail_753_, 2);
lean_dec_ref(v_alt_746_);
lean_dec_ref(v_codomain_745_);
lean_dec(v_u_744_);
lean_dec_ref(v_e_743_);
return v___x_766_;
}
}
else
{
lean_dec(v_head_763_);
lean_del_object(v___x_761_);
lean_dec(v_head_759_);
lean_dec_ref_known(v_tail_753_, 2);
lean_dec_ref(v_alt_746_);
lean_dec_ref(v_codomain_745_);
lean_dec(v_u_744_);
lean_dec_ref(v_e_743_);
return v___x_764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(lean_object* v___x_817_, lean_object* v___x_818_, lean_object* v_arg_819_, lean_object* v_arg_820_, lean_object* v_x_821_, lean_object* v___x_822_, lean_object* v_a_823_, lean_object* v_alt_824_, lean_object* v___x_825_, lean_object* v_tail_826_, lean_object* v_u_827_, uint8_t v___x_828_, uint8_t v___x_829_, uint8_t v___x_830_, lean_object* v_y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6));
v___x_838_ = l_Lean_Name_mkStr2(v___x_817_, v___x_837_);
v___x_839_ = l_Lean_Expr_const___override(v___x_838_, v___x_818_);
lean_inc_ref_n(v_y_831_, 2);
lean_inc_ref(v_x_821_);
v___x_840_ = l_Lean_mkApp4(v___x_839_, v_arg_819_, v_arg_820_, v_x_821_, v_y_831_);
v___x_841_ = lean_array_push(v___x_822_, v___x_840_);
v___x_842_ = l_Lean_Expr_beta(v_a_823_, v___x_841_);
v___x_843_ = l_Lean_Expr_beta(v_alt_824_, v___x_825_);
v___x_844_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_tail_826_, v_y_831_, v_u_827_, v___x_842_, v___x_843_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = lean_unsigned_to_nat(2u);
v___x_847_ = lean_mk_empty_array_with_capacity(v___x_846_);
v___x_848_ = lean_array_push(v___x_847_, v_x_821_);
v___x_849_ = lean_array_push(v___x_848_, v_y_831_);
v___x_850_ = l_Lean_Meta_mkLambdaFVars(v___x_849_, v_a_845_, v___x_828_, v___x_829_, v___x_828_, v___x_829_, v___x_830_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec_ref(v___x_849_);
return v___x_850_;
}
else
{
lean_dec_ref(v_y_831_);
lean_dec_ref(v_x_821_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_851_ = _args[0];
lean_object* v___x_852_ = _args[1];
lean_object* v_arg_853_ = _args[2];
lean_object* v_arg_854_ = _args[3];
lean_object* v_x_855_ = _args[4];
lean_object* v___x_856_ = _args[5];
lean_object* v_a_857_ = _args[6];
lean_object* v_alt_858_ = _args[7];
lean_object* v___x_859_ = _args[8];
lean_object* v_tail_860_ = _args[9];
lean_object* v_u_861_ = _args[10];
lean_object* v___x_862_ = _args[11];
lean_object* v___x_863_ = _args[12];
lean_object* v___x_864_ = _args[13];
lean_object* v_y_865_ = _args[14];
lean_object* v___y_866_ = _args[15];
lean_object* v___y_867_ = _args[16];
lean_object* v___y_868_ = _args[17];
lean_object* v___y_869_ = _args[18];
lean_object* v___y_870_ = _args[19];
_start:
{
uint8_t v___x_2949__boxed_871_; uint8_t v___x_2950__boxed_872_; uint8_t v___x_2951__boxed_873_; lean_object* v_res_874_; 
v___x_2949__boxed_871_ = lean_unbox(v___x_862_);
v___x_2950__boxed_872_ = lean_unbox(v___x_863_);
v___x_2951__boxed_873_ = lean_unbox(v___x_864_);
v_res_874_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(v___x_851_, v___x_852_, v_arg_853_, v_arg_854_, v_x_855_, v___x_856_, v_a_857_, v_alt_858_, v___x_859_, v_tail_860_, v_u_861_, v___x_2949__boxed_871_, v___x_2950__boxed_872_, v___x_2951__boxed_873_, v_y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(lean_object* v___x_875_, lean_object* v___x_876_, lean_object* v___x_877_, lean_object* v_arg_878_, lean_object* v_arg_879_, lean_object* v_a_880_, lean_object* v_alt_881_, lean_object* v_tail_882_, lean_object* v_u_883_, uint8_t v___x_884_, uint8_t v___x_885_, uint8_t v___x_886_, lean_object* v_head_887_, lean_object* v_x_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
lean_inc_ref(v_x_888_);
lean_inc_ref(v___x_875_);
v___x_894_ = lean_array_push(v___x_875_, v_x_888_);
v___x_895_ = lean_box(v___x_884_);
v___x_896_ = lean_box(v___x_885_);
v___x_897_ = lean_box(v___x_886_);
lean_inc_ref(v___x_894_);
lean_inc_ref(v_arg_879_);
v___f_898_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed), 20, 14);
lean_closure_set(v___f_898_, 0, v___x_876_);
lean_closure_set(v___f_898_, 1, v___x_877_);
lean_closure_set(v___f_898_, 2, v_arg_878_);
lean_closure_set(v___f_898_, 3, v_arg_879_);
lean_closure_set(v___f_898_, 4, v_x_888_);
lean_closure_set(v___f_898_, 5, v___x_875_);
lean_closure_set(v___f_898_, 6, v_a_880_);
lean_closure_set(v___f_898_, 7, v_alt_881_);
lean_closure_set(v___f_898_, 8, v___x_894_);
lean_closure_set(v___f_898_, 9, v_tail_882_);
lean_closure_set(v___f_898_, 10, v_u_883_);
lean_closure_set(v___f_898_, 11, v___x_895_);
lean_closure_set(v___f_898_, 12, v___x_896_);
lean_closure_set(v___f_898_, 13, v___x_897_);
v___x_899_ = l_Lean_Expr_beta(v_arg_879_, v___x_894_);
v___x_900_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_887_, v___x_899_, v___f_898_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___boxed(lean_object* v_varNames_901_, lean_object* v_e_902_, lean_object* v_u_903_, lean_object* v_codomain_904_, lean_object* v_alt_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_varNames_901_, v_e_902_, v_u_903_, v_codomain_904_, v_alt_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(lean_object* v_00_u03b1_912_, lean_object* v_msg_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___boxed(lean_object* v_00_u03b1_920_, lean_object* v_msg_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(v_00_u03b1_920_, v_msg_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v_res_927_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_930_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_931_ = lean_unsigned_to_nat(23u);
v___x_932_ = lean_unsigned_to_nat(183u);
v___x_933_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0));
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_935_ = l_mkPanicMessageWithDecl(v___x_934_, v___x_933_, v___x_932_, v___x_931_, v___x_930_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v_varNames_938_, lean_object* v_e_939_, uint8_t v___x_940_, uint8_t v___x_941_, lean_object* v_xs_942_, lean_object* v_codomain_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_array_get_size(v_xs_942_);
v___x_950_ = lean_nat_dec_eq(v___x_949_, v___x_936_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec_ref(v_codomain_943_);
lean_dec_ref(v_e_939_);
lean_dec_ref(v_varNames_938_);
v___x_951_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2);
v___x_952_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_951_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_952_;
}
else
{
lean_object* v___x_953_; 
lean_inc_ref(v_codomain_943_);
v___x_953_ = l_Lean_Meta_getLevel(v_codomain_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = lean_array_fget_borrowed(v_xs_942_, v___x_937_);
v___x_956_ = lean_array_to_list(v_varNames_938_);
lean_inc(v___x_955_);
v___x_957_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v___x_956_, v___x_955_, v_a_954_, v_codomain_943_, v_e_939_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; lean_object* v___x_962_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = lean_mk_empty_array_with_capacity(v___x_936_);
lean_inc(v___x_955_);
v___x_960_ = lean_array_push(v___x_959_, v___x_955_);
v___x_961_ = 1;
v___x_962_ = l_Lean_Meta_mkLambdaFVars(v___x_960_, v_a_958_, v___x_940_, v___x_941_, v___x_940_, v___x_941_, v___x_961_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec_ref(v___x_960_);
return v___x_962_;
}
else
{
return v___x_957_;
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec_ref(v_codomain_943_);
lean_dec_ref(v_e_939_);
lean_dec_ref(v_varNames_938_);
v_a_963_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_953_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_953_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed(lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v_varNames_973_, lean_object* v_e_974_, lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v_xs_977_, lean_object* v_codomain_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
uint8_t v___x_798__boxed_984_; uint8_t v___x_799__boxed_985_; lean_object* v_res_986_; 
v___x_798__boxed_984_ = lean_unbox(v___x_975_);
v___x_799__boxed_985_ = lean_unbox(v___x_976_);
v_res_986_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(v___x_971_, v___x_972_, v_varNames_973_, v_e_974_, v___x_798__boxed_984_, v___x_799__boxed_985_, v_xs_977_, v_codomain_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec_ref(v_xs_977_);
lean_dec(v___x_972_);
lean_dec(v___x_971_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry(lean_object* v_varNames_992_, lean_object* v_e_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = lean_array_get_size(v_varNames_992_);
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_nat_dec_eq(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; 
lean_inc(v_a_997_);
lean_inc_ref(v_a_996_);
lean_inc(v_a_995_);
lean_inc_ref(v_a_994_);
lean_inc_ref(v_e_993_);
v___x_1002_ = lean_infer_type(v_e_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
lean_inc_ref(v_varNames_992_);
v___x_1004_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_992_, v_a_1003_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = 1;
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_box(v___x_1001_);
v___x_1009_ = lean_box(v___x_1006_);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1010_, 0, v___x_1007_);
lean_closure_set(v___f_1010_, 1, v___x_1000_);
lean_closure_set(v___f_1010_, 2, v_varNames_992_);
lean_closure_set(v___f_1010_, 3, v_e_993_);
lean_closure_set(v___f_1010_, 4, v___x_1008_);
lean_closure_set(v___f_1010_, 5, v___x_1009_);
v___x_1011_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1012_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_1005_, v___x_1011_, v___f_1010_, v___x_1001_, v___x_1001_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1012_;
}
else
{
lean_dec_ref(v_e_993_);
lean_dec_ref(v_varNames_992_);
return v___x_1004_;
}
}
else
{
lean_dec_ref(v_e_993_);
lean_dec_ref(v_varNames_992_);
return v___x_1002_;
}
}
else
{
lean_object* v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v_varNames_992_);
v___x_1013_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_1014_ = 0;
v___x_1015_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_1016_ = l_Lean_mkLambda(v___x_1013_, v___x_1014_, v___x_1015_, v_e_993_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___boxed(lean_object* v_varNames_1018_, lean_object* v_e_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_varNames_1018_, v_e_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
return v_res_1025_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_dummy_1031_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1));
v_dummy_1031_ = l_Lean_Expr_const___override(v___x_1030_, v___x_1029_);
return v_dummy_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(lean_object* v_args_1032_, lean_object* v_type_1033_, lean_object* v_packedDomain_1034_, lean_object* v_tail_1035_, lean_object* v_x_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_dummy_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v_dummy_1042_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1036_);
v___x_1043_ = lean_array_push(v_args_1032_, v_x_1036_);
v___x_1044_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1033_, v_packedDomain_1034_, v_dummy_1042_, v___x_1043_, v_tail_1035_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; uint8_t v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_mk_empty_array_with_capacity(v___x_1046_);
v___x_1048_ = lean_array_push(v___x_1047_, v_x_1036_);
v___x_1049_ = 0;
v___x_1050_ = 1;
v___x_1051_ = 1;
v___x_1052_ = l_Lean_Meta_mkForallFVars(v___x_1048_, v_a_1045_, v___x_1049_, v___x_1050_, v___x_1050_, v___x_1051_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec_ref(v___x_1048_);
return v___x_1052_;
}
else
{
lean_dec_ref(v_x_1036_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed(lean_object* v_args_1053_, lean_object* v_type_1054_, lean_object* v_packedDomain_1055_, lean_object* v_tail_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(v_args_1053_, v_type_1054_, v_packedDomain_1055_, v_tail_1056_, v_x_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed(lean_object* v_arg_1064_, lean_object* v_args_1065_, lean_object* v_type_1066_, lean_object* v_packedDomain_1067_, lean_object* v_tail_1068_, lean_object* v___x_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v___x_724__boxed_1076_; lean_object* v_res_1077_; 
v___x_724__boxed_1076_ = lean_unbox(v___x_1069_);
v_res_1077_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(v_arg_1064_, v_args_1065_, v_type_1066_, v_packedDomain_1067_, v_tail_1068_, v___x_724__boxed_1076_, v_x_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(lean_object* v_type_1078_, lean_object* v_packedDomain_1079_, lean_object* v_domain_1080_, lean_object* v_args_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; 
if (lean_obj_tag(v_a_1082_) == 0)
{
lean_object* v_packedArg_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref(v_domain_1080_);
v_packedArg_1097_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1079_, v_args_1081_);
lean_dec_ref(v_args_1081_);
lean_dec_ref(v_packedDomain_1079_);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_mk_empty_array_with_capacity(v___x_1098_);
v___x_1100_ = lean_array_push(v___x_1099_, v_packedArg_1097_);
v___x_1101_ = l_Lean_Meta_instantiateForall(v_type_1078_, v___x_1100_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec_ref(v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v_tail_1102_; 
v_tail_1102_ = lean_ctor_get(v_a_1082_, 1);
lean_inc(v_tail_1102_);
if (lean_obj_tag(v_tail_1102_) == 0)
{
lean_object* v_head_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; 
v_head_1103_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_head_1103_);
lean_dec_ref_known(v_a_1082_, 2);
v___f_1104_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1104_, 0, v_args_1081_);
lean_closure_set(v___f_1104_, 1, v_type_1078_);
lean_closure_set(v___f_1104_, 2, v_packedDomain_1079_);
lean_closure_set(v___f_1104_, 3, v_tail_1102_);
v___x_1105_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1103_, v_domain_1080_, v___f_1104_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1105_;
}
else
{
lean_object* v_head_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_head_1106_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_head_1106_);
lean_dec_ref_known(v_a_1082_, 2);
lean_inc_ref(v_domain_1080_);
v___x_1107_ = l_Lean_Expr_cleanupAnnotations(v_domain_1080_);
v___x_1108_ = l_Lean_Expr_isApp(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v___x_1107_);
lean_dec(v_head_1106_);
lean_dec(v_tail_1102_);
lean_dec_ref(v_args_1081_);
lean_dec_ref(v_packedDomain_1079_);
lean_dec_ref(v_type_1078_);
v___y_1089_ = v_a_1083_;
v___y_1090_ = v_a_1084_;
v___y_1091_ = v_a_1085_;
v___y_1092_ = v_a_1086_;
goto v___jp_1088_;
}
else
{
lean_object* v_arg_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_arg_1109_ = lean_ctor_get(v___x_1107_, 1);
lean_inc_ref(v_arg_1109_);
v___x_1110_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1107_);
v___x_1111_ = l_Lean_Expr_isApp(v___x_1110_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_arg_1109_);
lean_dec(v_head_1106_);
lean_dec(v_tail_1102_);
lean_dec_ref(v_args_1081_);
lean_dec_ref(v_packedDomain_1079_);
lean_dec_ref(v_type_1078_);
v___y_1089_ = v_a_1083_;
v___y_1090_ = v_a_1084_;
v___y_1091_ = v_a_1085_;
v___y_1092_ = v_a_1086_;
goto v___jp_1088_;
}
else
{
lean_object* v_arg_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_arg_1112_ = lean_ctor_get(v___x_1110_, 1);
lean_inc_ref(v_arg_1112_);
v___x_1113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1110_);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1115_ = l_Lean_Expr_isConstOf(v___x_1113_, v___x_1114_);
lean_dec_ref(v___x_1113_);
if (v___x_1115_ == 0)
{
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_arg_1109_);
lean_dec(v_head_1106_);
lean_dec(v_tail_1102_);
lean_dec_ref(v_args_1081_);
lean_dec_ref(v_packedDomain_1079_);
lean_dec_ref(v_type_1078_);
v___y_1089_ = v_a_1083_;
v___y_1090_ = v_a_1084_;
v___y_1091_ = v_a_1085_;
v___y_1092_ = v_a_1086_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; 
lean_dec_ref(v_domain_1080_);
v___x_1116_ = lean_box(v___x_1115_);
v___f_1117_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1117_, 0, v_arg_1109_);
lean_closure_set(v___f_1117_, 1, v_args_1081_);
lean_closure_set(v___f_1117_, 2, v_type_1078_);
lean_closure_set(v___f_1117_, 3, v_packedDomain_1079_);
lean_closure_set(v___f_1117_, 4, v_tail_1102_);
lean_closure_set(v___f_1117_, 5, v___x_1116_);
v___x_1118_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1106_, v_arg_1112_, v___f_1117_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1118_;
}
}
}
}
}
v___jp_1088_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1093_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1);
v___x_1094_ = l_Lean_MessageData_ofExpr(v_domain_1080_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1095_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(lean_object* v_arg_1119_, lean_object* v_args_1120_, lean_object* v_type_1121_, lean_object* v_packedDomain_1122_, lean_object* v_tail_1123_, uint8_t v___x_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1131_);
lean_inc_ref(v_x_1125_);
v___x_1133_ = lean_array_push(v___x_1132_, v_x_1125_);
lean_inc_ref(v___x_1133_);
v___x_1134_ = l_Lean_Expr_beta(v_arg_1119_, v___x_1133_);
v___x_1135_ = lean_array_push(v_args_1120_, v_x_1125_);
v___x_1136_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1121_, v_packedDomain_1122_, v___x_1134_, v___x_1135_, v_tail_1123_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; uint8_t v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v___x_1138_ = 0;
v___x_1139_ = 1;
v___x_1140_ = l_Lean_Meta_mkForallFVars(v___x_1133_, v_a_1137_, v___x_1138_, v___x_1124_, v___x_1124_, v___x_1139_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec_ref(v___x_1133_);
return v___x_1140_;
}
else
{
lean_dec_ref(v___x_1133_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___boxed(lean_object* v_type_1141_, lean_object* v_packedDomain_1142_, lean_object* v_domain_1143_, lean_object* v_args_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1141_, v_packedDomain_1142_, v_domain_1143_, v_args_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1151_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(lean_object* v_varNames_1155_, lean_object* v_type_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; uint8_t v___x_1171_; 
v___x_1171_ = l_Lean_Expr_isForall(v_type_1156_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_varNames_1155_);
v___x_1172_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_1173_ = l_Lean_MessageData_ofExpr(v_type_1156_);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1174_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
v___y_1163_ = v_a_1157_;
v___y_1164_ = v_a_1158_;
v___y_1165_ = v_a_1159_;
v___y_1166_ = v_a_1160_;
goto v___jp_1162_;
}
v___jp_1162_:
{
lean_object* v_packedDomain_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_packedDomain_1167_ = l_Lean_Expr_bindingDomain_x21(v_type_1156_);
v___x_1168_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_1169_ = lean_array_to_list(v_varNames_1155_);
lean_inc_ref(v_packedDomain_1167_);
v___x_1170_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1156_, v_packedDomain_1167_, v_packedDomain_1167_, v___x_1168_, v___x_1169_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___boxed(lean_object* v_varNames_1184_, lean_object* v_type_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_varNames_1184_, v_type_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
return v_res_1191_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0));
v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(lean_object* v_args_1195_, lean_object* v_e_1196_, lean_object* v_packedDomain_1197_, lean_object* v_tail_1198_, lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_dummy_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_dummy_1205_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1199_);
v___x_1206_ = lean_array_push(v_args_1195_, v_x_1199_);
v___x_1207_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1196_, v_packedDomain_1197_, v_dummy_1205_, v___x_1206_, v_tail_1198_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; uint8_t v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_mk_empty_array_with_capacity(v___x_1209_);
v___x_1211_ = lean_array_push(v___x_1210_, v_x_1199_);
v___x_1212_ = 0;
v___x_1213_ = 1;
v___x_1214_ = 1;
v___x_1215_ = l_Lean_Meta_mkLambdaFVars(v___x_1211_, v_a_1208_, v___x_1212_, v___x_1213_, v___x_1212_, v___x_1213_, v___x_1214_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec_ref(v___x_1211_);
return v___x_1215_;
}
else
{
lean_dec_ref(v_x_1199_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed(lean_object* v_args_1216_, lean_object* v_e_1217_, lean_object* v_packedDomain_1218_, lean_object* v_tail_1219_, lean_object* v_x_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(v_args_1216_, v_e_1217_, v_packedDomain_1218_, v_tail_1219_, v_x_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed(lean_object* v_arg_1227_, lean_object* v_args_1228_, lean_object* v_e_1229_, lean_object* v_packedDomain_1230_, lean_object* v_tail_1231_, lean_object* v___x_1232_, lean_object* v_x_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___x_842__boxed_1239_; lean_object* v_res_1240_; 
v___x_842__boxed_1239_ = lean_unbox(v___x_1232_);
v_res_1240_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(v_arg_1227_, v_args_1228_, v_e_1229_, v_packedDomain_1230_, v_tail_1231_, v___x_842__boxed_1239_, v_x_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(lean_object* v_e_1241_, lean_object* v_packedDomain_1242_, lean_object* v_domain_1243_, lean_object* v_args_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; 
if (lean_obj_tag(v_a_1245_) == 0)
{
lean_object* v_packedArg_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec_ref(v_domain_1243_);
v_packedArg_1260_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1242_, v_args_1244_);
lean_dec_ref(v_args_1244_);
lean_dec_ref(v_packedDomain_1242_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_mk_empty_array_with_capacity(v___x_1261_);
v___x_1263_ = lean_array_push(v___x_1262_, v_packedArg_1260_);
v___x_1264_ = l_Lean_Expr_beta(v_e_1241_, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
else
{
lean_object* v_tail_1266_; 
v_tail_1266_ = lean_ctor_get(v_a_1245_, 1);
lean_inc(v_tail_1266_);
if (lean_obj_tag(v_tail_1266_) == 0)
{
lean_object* v_head_1267_; lean_object* v___f_1268_; lean_object* v___x_1269_; 
v_head_1267_ = lean_ctor_get(v_a_1245_, 0);
lean_inc(v_head_1267_);
lean_dec_ref_known(v_a_1245_, 2);
v___f_1268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1268_, 0, v_args_1244_);
lean_closure_set(v___f_1268_, 1, v_e_1241_);
lean_closure_set(v___f_1268_, 2, v_packedDomain_1242_);
lean_closure_set(v___f_1268_, 3, v_tail_1266_);
v___x_1269_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1267_, v_domain_1243_, v___f_1268_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1269_;
}
else
{
lean_object* v_head_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_head_1270_ = lean_ctor_get(v_a_1245_, 0);
lean_inc(v_head_1270_);
lean_dec_ref_known(v_a_1245_, 2);
lean_inc_ref(v_domain_1243_);
v___x_1271_ = l_Lean_Expr_cleanupAnnotations(v_domain_1243_);
v___x_1272_ = l_Lean_Expr_isApp(v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec_ref(v___x_1271_);
lean_dec(v_head_1270_);
lean_dec(v_tail_1266_);
lean_dec_ref(v_args_1244_);
lean_dec_ref(v_packedDomain_1242_);
lean_dec_ref(v_e_1241_);
v___y_1252_ = v_a_1246_;
v___y_1253_ = v_a_1247_;
v___y_1254_ = v_a_1248_;
v___y_1255_ = v_a_1249_;
goto v___jp_1251_;
}
else
{
lean_object* v_arg_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_arg_1273_ = lean_ctor_get(v___x_1271_, 1);
lean_inc_ref(v_arg_1273_);
v___x_1274_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1271_);
v___x_1275_ = l_Lean_Expr_isApp(v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_arg_1273_);
lean_dec(v_head_1270_);
lean_dec(v_tail_1266_);
lean_dec_ref(v_args_1244_);
lean_dec_ref(v_packedDomain_1242_);
lean_dec_ref(v_e_1241_);
v___y_1252_ = v_a_1246_;
v___y_1253_ = v_a_1247_;
v___y_1254_ = v_a_1248_;
v___y_1255_ = v_a_1249_;
goto v___jp_1251_;
}
else
{
lean_object* v_arg_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_arg_1276_ = lean_ctor_get(v___x_1274_, 1);
lean_inc_ref(v_arg_1276_);
v___x_1277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1274_);
v___x_1278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1279_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1278_);
lean_dec_ref(v___x_1277_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
lean_dec(v_head_1270_);
lean_dec(v_tail_1266_);
lean_dec_ref(v_args_1244_);
lean_dec_ref(v_packedDomain_1242_);
lean_dec_ref(v_e_1241_);
v___y_1252_ = v_a_1246_;
v___y_1253_ = v_a_1247_;
v___y_1254_ = v_a_1248_;
v___y_1255_ = v_a_1249_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; 
lean_dec_ref(v_domain_1243_);
v___x_1280_ = lean_box(v___x_1279_);
v___f_1281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1281_, 0, v_arg_1273_);
lean_closure_set(v___f_1281_, 1, v_args_1244_);
lean_closure_set(v___f_1281_, 2, v_e_1241_);
lean_closure_set(v___f_1281_, 3, v_packedDomain_1242_);
lean_closure_set(v___f_1281_, 4, v_tail_1266_);
lean_closure_set(v___f_1281_, 5, v___x_1280_);
v___x_1282_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1270_, v_arg_1276_, v___f_1281_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
return v___x_1282_;
}
}
}
}
}
v___jp_1251_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1);
v___x_1257_ = l_Lean_MessageData_ofExpr(v_domain_1243_);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1258_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(lean_object* v_arg_1283_, lean_object* v_args_1284_, lean_object* v_e_1285_, lean_object* v_packedDomain_1286_, lean_object* v_tail_1287_, uint8_t v___x_1288_, lean_object* v_x_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_mk_empty_array_with_capacity(v___x_1295_);
lean_inc_ref(v_x_1289_);
v___x_1297_ = lean_array_push(v___x_1296_, v_x_1289_);
lean_inc_ref(v___x_1297_);
v___x_1298_ = l_Lean_Expr_beta(v_arg_1283_, v___x_1297_);
v___x_1299_ = lean_array_push(v_args_1284_, v_x_1289_);
v___x_1300_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1285_, v_packedDomain_1286_, v___x_1298_, v___x_1299_, v_tail_1287_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; uint8_t v___x_1302_; uint8_t v___x_1303_; lean_object* v___x_1304_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = 0;
v___x_1303_ = 1;
v___x_1304_ = l_Lean_Meta_mkLambdaFVars(v___x_1297_, v_a_1301_, v___x_1302_, v___x_1288_, v___x_1302_, v___x_1288_, v___x_1303_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec_ref(v___x_1297_);
return v___x_1304_;
}
else
{
lean_dec_ref(v___x_1297_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___boxed(lean_object* v_e_1305_, lean_object* v_packedDomain_1306_, lean_object* v_domain_1307_, lean_object* v_args_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1305_, v_packedDomain_1306_, v_domain_1307_, v_args_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1315_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0));
v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_pack___closed__2, &l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2);
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_mk_empty_array_with_capacity(v___x_1320_);
v___x_1322_ = lean_array_push(v___x_1321_, v___x_1319_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(lean_object* v_varNames_1323_, lean_object* v_e_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1330_ = lean_array_get_size(v_varNames_1323_);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_nat_dec_eq(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_inc(v_a_1328_);
lean_inc_ref(v_a_1327_);
lean_inc(v_a_1326_);
lean_inc_ref(v_a_1325_);
lean_inc_ref(v_e_1324_);
v___x_1333_ = lean_infer_type(v_e_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1335_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = l_Lean_Meta_whnfForall(v_a_1334_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; uint8_t v___x_1346_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___x_1346_ = l_Lean_Expr_isForall(v_a_1336_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_e_1324_);
lean_dec_ref(v_varNames_1323_);
v___x_1347_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1);
v___x_1348_ = l_Lean_MessageData_ofExpr(v_a_1336_);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1349_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
else
{
v___y_1338_ = v_a_1325_;
v___y_1339_ = v_a_1326_;
v___y_1340_ = v_a_1327_;
v___y_1341_ = v_a_1328_;
goto v___jp_1337_;
}
v___jp_1337_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = l_Lean_Expr_bindingDomain_x21(v_a_1336_);
lean_dec(v_a_1336_);
v___x_1343_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_1344_ = lean_array_to_list(v_varNames_1323_);
lean_inc_ref(v___x_1342_);
v___x_1345_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1324_, v___x_1342_, v___x_1342_, v___x_1343_, v___x_1344_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1345_;
}
}
else
{
lean_dec_ref(v_e_1324_);
lean_dec_ref(v_varNames_1323_);
return v___x_1335_;
}
}
else
{
lean_dec_ref(v_e_1324_);
lean_dec_ref(v_varNames_1323_);
return v___x_1333_;
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v_varNames_1323_);
v___x_1359_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2);
v___x_1360_ = l_Lean_Expr_beta(v_e_1324_, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___boxed(lean_object* v_varNames_1362_, lean_object* v_e_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v_varNames_1362_, v_e_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(lean_object* v_as_1373_, size_t v_sz_1374_, size_t v_i_1375_, lean_object* v_b_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_usize_dec_lt(v_i_1375_, v_sz_1374_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_b_1376_);
return v___x_1383_;
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_a_1384_ = lean_array_uget_borrowed(v_as_1373_, v_i_1375_);
v___x_1385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1386_ = lean_unsigned_to_nat(2u);
v___x_1387_ = lean_mk_empty_array_with_capacity(v___x_1386_);
lean_inc(v_a_1384_);
v___x_1388_ = lean_array_push(v___x_1387_, v_a_1384_);
v___x_1389_ = lean_array_push(v___x_1388_, v_b_1376_);
v___x_1390_ = l_Lean_Meta_mkAppM(v___x_1385_, v___x_1389_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; size_t v___x_1392_; size_t v___x_1393_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = lean_usize_add(v_i_1375_, v___x_1392_);
v_i_1375_ = v___x_1393_;
v_b_1376_ = v_a_1391_;
goto _start;
}
else
{
return v___x_1390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___boxed(lean_object* v_as_1395_, lean_object* v_sz_1396_, lean_object* v_i_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
size_t v_sz_boxed_1404_; size_t v_i_boxed_1405_; lean_object* v_res_1406_; 
v_sz_boxed_1404_ = lean_unbox_usize(v_sz_1396_);
lean_dec(v_sz_1396_);
v_i_boxed_1405_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v_as_1395_, v_sz_boxed_1404_, v_i_boxed_1405_, v_b_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v_as_1395_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object* v_ds_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_r_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v_sz_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1413_ = l_Lean_instInhabitedExpr;
v___x_1414_ = lean_array_get_size(v_ds_1407_);
v___x_1415_ = lean_unsigned_to_nat(1u);
v___x_1416_ = lean_nat_sub(v___x_1414_, v___x_1415_);
v_r_1417_ = lean_array_get(v___x_1413_, v_ds_1407_, v___x_1416_);
lean_dec(v___x_1416_);
v___x_1418_ = lean_array_pop(v_ds_1407_);
v___x_1419_ = l_Array_reverse___redArg(v___x_1418_);
v_sz_1420_ = lean_array_size(v___x_1419_);
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v___x_1419_, v_sz_1420_, v___x_1421_, v_r_1417_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec_ref(v___x_1419_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object* v_ds_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v_ds_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
return v_res_1429_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object* v_n_1433_, lean_object* v_type_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v_zero_1449_; uint8_t v_isZero_1450_; 
v_zero_1449_ = lean_unsigned_to_nat(0u);
v_isZero_1450_ = lean_nat_dec_eq(v_n_1433_, v_zero_1449_);
if (v_isZero_1450_ == 1)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v_type_1434_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
else
{
lean_object* v_one_1453_; lean_object* v_n_1454_; uint8_t v___x_1455_; 
v_one_1453_ = lean_unsigned_to_nat(1u);
v_n_1454_ = lean_nat_sub(v_n_1433_, v_one_1453_);
v___x_1455_ = lean_nat_dec_eq(v_n_1454_, v_zero_1449_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
lean_inc_ref(v_type_1434_);
v___x_1456_ = l_Lean_Expr_cleanupAnnotations(v_type_1434_);
v___x_1457_ = l_Lean_Expr_isApp(v___x_1456_);
if (v___x_1457_ == 0)
{
lean_dec_ref(v___x_1456_);
lean_dec(v_n_1454_);
v___y_1441_ = v_a_1435_;
v___y_1442_ = v_a_1436_;
v___y_1443_ = v_a_1437_;
v___y_1444_ = v_a_1438_;
goto v___jp_1440_;
}
else
{
lean_object* v_arg_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_arg_1458_ = lean_ctor_get(v___x_1456_, 1);
lean_inc_ref(v_arg_1458_);
v___x_1459_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1456_);
v___x_1460_ = l_Lean_Expr_isApp(v___x_1459_);
if (v___x_1460_ == 0)
{
lean_dec_ref(v___x_1459_);
lean_dec_ref(v_arg_1458_);
lean_dec(v_n_1454_);
v___y_1441_ = v_a_1435_;
v___y_1442_ = v_a_1436_;
v___y_1443_ = v_a_1437_;
v___y_1444_ = v_a_1438_;
goto v___jp_1440_;
}
else
{
lean_object* v_arg_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_arg_1461_ = lean_ctor_get(v___x_1459_, 1);
lean_inc_ref(v_arg_1461_);
v___x_1462_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1459_);
v___x_1463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1464_ = l_Lean_Expr_isConstOf(v___x_1462_, v___x_1463_);
lean_dec_ref(v___x_1462_);
if (v___x_1464_ == 0)
{
lean_dec_ref(v_arg_1461_);
lean_dec_ref(v_arg_1458_);
lean_dec(v_n_1454_);
v___y_1441_ = v_a_1435_;
v___y_1442_ = v_a_1436_;
v___y_1443_ = v_a_1437_;
v___y_1444_ = v_a_1438_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1465_; 
lean_dec_ref(v_type_1434_);
v___x_1465_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1454_, v_arg_1458_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_n_1454_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_arg_1461_);
lean_ctor_set(v___x_1470_, 1, v_a_1466_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_dec_ref(v_arg_1461_);
return v___x_1465_;
}
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec(v_n_1454_);
v___x_1475_ = lean_box(0);
v___x_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_type_1434_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
}
v___jp_1440_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1445_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1);
v___x_1446_ = l_Lean_MessageData_ofExpr(v_type_1434_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1447_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object* v_n_1478_, lean_object* v_type_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1478_, v_type_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_n_1478_);
return v_res_1485_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0(void){
_start:
{
lean_object* v___x_1486_; lean_object* v_dummy_1487_; 
v___x_1486_ = lean_box(0);
v_dummy_1487_ = l_Lean_Expr_sort___override(v___x_1486_);
return v_dummy_1487_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1490_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1));
v___x_1491_ = lean_unsigned_to_nat(8u);
v___x_1492_ = lean_unsigned_to_nat(279u);
v___x_1493_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0));
v___x_1494_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1495_ = l_mkPanicMessageWithDecl(v___x_1494_, v___x_1493_, v___x_1492_, v___x_1491_, v___x_1490_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(lean_object* v_i_1504_, lean_object* v_fidx_1505_, lean_object* v_numFuncs_1506_, lean_object* v_arg_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_x_1508_) == 5)
{
lean_object* v_fn_1517_; lean_object* v_arg_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_fn_1517_ = lean_ctor_get(v_x_1508_, 0);
lean_inc_ref(v_fn_1517_);
v_arg_1518_ = lean_ctor_get(v_x_1508_, 1);
lean_inc_ref(v_arg_1518_);
lean_dec_ref_known(v_x_1508_, 2);
v___x_1519_ = lean_array_set(v_x_1509_, v_x_1510_, v_arg_1518_);
v___x_1520_ = lean_nat_sub(v_x_1510_, v___x_1516_);
lean_dec(v_x_1510_);
v_x_1508_ = v_fn_1517_;
v_x_1509_ = v___x_1519_;
v_x_1510_ = v___x_1520_;
goto _start;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
lean_dec(v_x_1510_);
v___x_1522_ = lean_array_get_size(v_x_1509_);
v___x_1523_ = lean_unsigned_to_nat(2u);
v___x_1524_ = lean_nat_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v_x_1509_);
lean_dec_ref(v_x_1508_);
lean_dec_ref(v_arg_1507_);
v___x_1525_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2);
v___x_1526_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1525_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = l_Lean_instInhabitedExpr;
v___x_1528_ = lean_nat_dec_eq(v_i_1504_, v_fidx_1505_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = lean_nat_add(v_i_1504_, v___x_1516_);
v___x_1530_ = lean_array_get(v___x_1527_, v_x_1509_, v___x_1516_);
lean_inc(v___x_1530_);
v___x_1531_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1506_, v_fidx_1505_, v_arg_1507_, v___x_1529_, v___x_1530_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___x_1529_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1545_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1545_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1545_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1536_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1537_ = l_Lean_Expr_constLevels_x21(v_x_1508_);
lean_dec_ref(v_x_1508_);
v___x_1538_ = l_Lean_mkConst(v___x_1536_, v___x_1537_);
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = lean_array_get(v___x_1527_, v_x_1509_, v___x_1539_);
lean_dec_ref(v_x_1509_);
v___x_1541_ = l_Lean_mkApp3(v___x_1538_, v___x_1540_, v___x_1530_, v_a_1532_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1541_);
v___x_1543_ = v___x_1534_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_dec(v___x_1530_);
lean_dec_ref(v_x_1509_);
lean_dec_ref(v_x_1508_);
return v___x_1531_;
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1546_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1547_ = l_Lean_Expr_constLevels_x21(v_x_1508_);
lean_dec_ref(v_x_1508_);
v___x_1548_ = l_Lean_mkConst(v___x_1546_, v___x_1547_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = lean_array_get(v___x_1527_, v_x_1509_, v___x_1549_);
v___x_1551_ = lean_array_get(v___x_1527_, v_x_1509_, v___x_1516_);
lean_dec_ref(v_x_1509_);
v___x_1552_ = l_Lean_mkApp3(v___x_1548_, v___x_1550_, v___x_1551_, v_arg_1507_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(lean_object* v_numFuncs_1554_, lean_object* v_fidx_1555_, lean_object* v_arg_1556_, lean_object* v_i_1557_, lean_object* v_type_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_sub(v_numFuncs_1554_, v___x_1564_);
v___x_1566_ = lean_nat_dec_le(v___x_1565_, v_i_1557_);
lean_dec(v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Meta_whnfD(v_type_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_dummy_1569_; lean_object* v_nargs_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v_dummy_1569_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
v_nargs_1570_ = l_Lean_Expr_getAppNumArgs(v_a_1568_);
lean_inc(v_nargs_1570_);
v___x_1571_ = lean_mk_array(v_nargs_1570_, v_dummy_1569_);
v___x_1572_ = lean_nat_sub(v_nargs_1570_, v___x_1564_);
lean_dec(v_nargs_1570_);
v___x_1573_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1557_, v_fidx_1555_, v_numFuncs_1554_, v_arg_1556_, v_a_1568_, v___x_1571_, v___x_1572_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
return v___x_1573_;
}
else
{
lean_dec_ref(v_arg_1556_);
return v___x_1567_;
}
}
else
{
lean_object* v___x_1574_; 
lean_dec_ref(v_type_1558_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_arg_1556_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___boxed(lean_object* v_numFuncs_1575_, lean_object* v_fidx_1576_, lean_object* v_arg_1577_, lean_object* v_i_1578_, lean_object* v_type_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1575_, v_fidx_1576_, v_arg_1577_, v_i_1578_, v_type_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_i_1578_);
lean_dec(v_fidx_1576_);
lean_dec(v_numFuncs_1575_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___boxed(lean_object* v_i_1586_, lean_object* v_fidx_1587_, lean_object* v_numFuncs_1588_, lean_object* v_arg_1589_, lean_object* v_x_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1586_, v_fidx_1587_, v_numFuncs_1588_, v_arg_1589_, v_x_1590_, v_x_1591_, v_x_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v_numFuncs_1588_);
lean_dec(v_fidx_1587_);
lean_dec(v_i_1586_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object* v_numFuncs_1599_, lean_object* v_domain_1600_, lean_object* v_fidx_1601_, lean_object* v_arg_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1599_, v_fidx_1601_, v_arg_1602_, v___x_1608_, v_domain_1600_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object* v_numFuncs_1610_, lean_object* v_domain_1611_, lean_object* v_fidx_1612_, lean_object* v_arg_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v_numFuncs_1610_, v_domain_1611_, v_fidx_1612_, v_arg_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_fidx_1612_);
lean_dec(v_numFuncs_1610_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(lean_object* v_numFuncs_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1658_; 
v_fst_1622_ = lean_ctor_get(v_a_1621_, 0);
v_snd_1623_ = lean_ctor_get(v_a_1621_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_a_1621_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1625_ = v_a_1621_;
v_isShared_1626_ = v_isSharedCheck_1658_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snd_1623_);
lean_inc(v_fst_1622_);
lean_dec(v_a_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1658_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1627_ = lean_unsigned_to_nat(1u);
v___x_1628_ = lean_nat_add(v_fst_1622_, v___x_1627_);
v___x_1629_ = lean_nat_dec_lt(v___x_1628_, v_numFuncs_1620_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1631_; 
lean_dec(v___x_1628_);
if (v_isShared_1626_ == 0)
{
v___x_1631_ = v___x_1625_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_fst_1622_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_snd_1623_);
v___x_1631_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1635_ = lean_unsigned_to_nat(3u);
v___x_1636_ = l_Lean_Expr_isAppOfArity(v_snd_1623_, v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
lean_dec(v___x_1628_);
v___x_1637_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1638_ = l_Lean_Expr_isAppOfArity(v_snd_1623_, v___x_1637_, v___x_1635_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_del_object(v___x_1625_);
lean_dec(v_snd_1623_);
lean_dec(v_fst_1622_);
v___x_1639_ = lean_box(0);
return v___x_1639_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1640_ = lean_unsigned_to_nat(2u);
v___x_1641_ = l_Lean_Expr_getAppNumArgs(v_snd_1623_);
v___x_1642_ = lean_nat_sub(v___x_1641_, v___x_1640_);
lean_dec(v___x_1641_);
v___x_1643_ = lean_nat_sub(v___x_1642_, v___x_1627_);
lean_dec(v___x_1642_);
v___x_1644_ = l_Lean_Expr_getRevArg_x21(v_snd_1623_, v___x_1643_);
lean_dec(v_snd_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v___x_1644_);
v___x_1646_ = v___x_1625_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_fst_1622_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_dec(v_fst_1622_);
v___x_1649_ = lean_unsigned_to_nat(2u);
v___x_1650_ = l_Lean_Expr_getAppNumArgs(v_snd_1623_);
v___x_1651_ = lean_nat_sub(v___x_1650_, v___x_1649_);
lean_dec(v___x_1650_);
v___x_1652_ = lean_nat_sub(v___x_1651_, v___x_1627_);
lean_dec(v___x_1651_);
v___x_1653_ = l_Lean_Expr_getRevArg_x21(v_snd_1623_, v___x_1652_);
lean_dec(v_snd_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v___x_1653_);
lean_ctor_set(v___x_1625_, 0, v___x_1628_);
v___x_1655_ = v___x_1625_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
v_a_1621_ = v___x_1655_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg___boxed(lean_object* v_numFuncs_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1659_, v_a_1660_);
lean_dec(v_numFuncs_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object* v_numFuncs_1662_, lean_object* v_expr_1663_){
_start:
{
lean_object* v_funidx_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_funidx_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v_funidx_1664_);
lean_ctor_set(v___x_1665_, 1, v_expr_1663_);
v___x_1666_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1662_, v___x_1665_);
if (lean_obj_tag(v___x_1666_) == 0)
{
return v___x_1666_;
}
else
{
lean_object* v_val_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1683_; 
v_val_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1683_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_val_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1683_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v_fst_1671_; lean_object* v_snd_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1682_; 
v_fst_1671_ = lean_ctor_get(v_val_1667_, 0);
v_snd_1672_ = lean_ctor_get(v_val_1667_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_val_1667_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1674_ = v_val_1667_;
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_snd_1672_);
lean_inc(v_fst_1671_);
lean_dec(v_val_1667_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_fst_1671_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_snd_1672_);
v___x_1677_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1679_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1677_);
v___x_1679_ = v___x_1669_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(lean_object* v_numFuncs_1684_, lean_object* v_expr_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v_numFuncs_1684_, v_expr_1685_);
lean_dec(v_numFuncs_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(lean_object* v_numFuncs_1687_, lean_object* v_inst_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1687_, v_a_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(lean_object* v_numFuncs_1691_, lean_object* v_inst_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(v_numFuncs_1691_, v_inst_1692_, v_a_1693_);
lean_dec(v_numFuncs_1691_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v_types_1697_, lean_object* v_i_1698_, uint8_t v___x_1699_, uint8_t v___x_1700_, uint8_t v___x_1701_, lean_object* v_x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_inc_ref(v_x_1702_);
v___x_1708_ = lean_array_push(v___x_1695_, v_x_1702_);
v___x_1709_ = lean_array_get_borrowed(v___x_1696_, v_types_1697_, v_i_1698_);
v___x_1710_ = l_Lean_Expr_bindingBody_x21(v___x_1709_);
v___x_1711_ = lean_expr_instantiate1(v___x_1710_, v_x_1702_);
lean_dec_ref(v_x_1702_);
lean_dec_ref(v___x_1710_);
v___x_1712_ = l_Lean_Meta_mkLambdaFVars(v___x_1708_, v___x_1711_, v___x_1699_, v___x_1700_, v___x_1699_, v___x_1700_, v___x_1701_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec_ref(v___x_1708_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object* v___x_1713_, lean_object* v___x_1714_, lean_object* v_types_1715_, lean_object* v_i_1716_, lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v___x_1663__boxed_1726_; uint8_t v___x_1664__boxed_1727_; uint8_t v___x_1665__boxed_1728_; lean_object* v_res_1729_; 
v___x_1663__boxed_1726_ = lean_unbox(v___x_1717_);
v___x_1664__boxed_1727_ = lean_unbox(v___x_1718_);
v___x_1665__boxed_1728_ = lean_unbox(v___x_1719_);
v_res_1729_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v___x_1713_, v___x_1714_, v_types_1715_, v_i_1716_, v___x_1663__boxed_1726_, v___x_1664__boxed_1727_, v___x_1665__boxed_1728_, v_x_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v_i_1716_);
lean_dec_ref(v_types_1715_);
lean_dec_ref(v___x_1714_);
return v_res_1729_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1732_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1));
v___x_1733_ = lean_unsigned_to_nat(6u);
v___x_1734_ = lean_unsigned_to_nat(321u);
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0));
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1737_ = l_mkPanicMessageWithDecl(v___x_1736_, v___x_1735_, v___x_1734_, v___x_1733_, v___x_1732_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object* v_i_1738_, lean_object* v___x_1739_, lean_object* v_types_1740_, lean_object* v_u_1741_, lean_object* v___x_1742_, lean_object* v___x_1743_, lean_object* v___x_1744_, lean_object* v___x_1745_, lean_object* v_x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_1723__boxed_1752_; uint8_t v___x_1724__boxed_1753_; uint8_t v___x_1725__boxed_1754_; lean_object* v_res_1755_; 
v___x_1723__boxed_1752_ = lean_unbox(v___x_1743_);
v___x_1724__boxed_1753_ = lean_unbox(v___x_1744_);
v___x_1725__boxed_1754_ = lean_unbox(v___x_1745_);
v_res_1755_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_i_1738_, v___x_1739_, v_types_1740_, v_u_1741_, v___x_1742_, v___x_1723__boxed_1752_, v___x_1724__boxed_1753_, v___x_1725__boxed_1754_, v_x_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___x_1739_);
lean_dec(v_i_1738_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object* v_types_1759_, lean_object* v_u_1760_, lean_object* v_x_1761_, lean_object* v_i_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1768_ = l_Lean_instInhabitedExpr;
v___x_1769_ = lean_array_get_size(v_types_1759_);
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_nat_sub(v___x_1769_, v___x_1770_);
v___x_1772_ = lean_nat_dec_lt(v_i_1762_, v___x_1771_);
lean_dec(v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v_u_1760_);
v___x_1773_ = lean_array_get(v___x_1768_, v_types_1759_, v_i_1762_);
lean_dec(v_i_1762_);
lean_dec_ref(v_types_1759_);
v___x_1774_ = l_Lean_Expr_bindingBody_x21(v___x_1773_);
lean_dec(v___x_1773_);
v___x_1775_ = lean_expr_instantiate1(v___x_1774_, v_x_1761_);
lean_dec_ref(v_x_1761_);
lean_dec_ref(v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; 
lean_inc(v_a_1766_);
lean_inc_ref(v_a_1765_);
lean_inc(v_a_1764_);
lean_inc_ref(v_a_1763_);
lean_inc_ref(v_x_1761_);
v___x_1777_ = lean_infer_type(v_x_1761_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = l_Lean_Meta_whnfD(v_a_1778_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1782_ = lean_unsigned_to_nat(2u);
v___x_1783_ = l_Lean_Expr_isAppOfArity(v_a_1780_, v___x_1781_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec(v_a_1780_);
lean_dec(v_i_1762_);
lean_dec_ref(v_x_1761_);
lean_dec(v_u_1760_);
lean_dec_ref(v_types_1759_);
v___x_1784_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
v___x_1785_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1784_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; 
lean_inc_n(v_u_1760_, 2);
v___x_1786_ = l_Lean_Level_succ___override(v_u_1760_);
v___x_1787_ = lean_mk_empty_array_with_capacity(v___x_1770_);
lean_inc_ref(v_x_1761_);
lean_inc_ref(v___x_1787_);
v___x_1788_ = lean_array_push(v___x_1787_, v_x_1761_);
v___x_1789_ = l_Lean_mkSort(v_u_1760_);
v___x_1790_ = 0;
v___x_1791_ = 1;
v___x_1792_ = l_Lean_Meta_mkLambdaFVars(v___x_1788_, v___x_1789_, v___x_1790_, v___x_1772_, v___x_1790_, v___x_1772_, v___x_1791_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec_ref(v___x_1788_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v___x_1794_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_1795_ = l_Lean_Core_mkFreshUserName(v___x_1794_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v_nargs_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___f_1801_; lean_object* v_dummy_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v_nargs_1797_ = l_Lean_Expr_getAppNumArgs(v_a_1780_);
v___x_1798_ = lean_box(v___x_1790_);
v___x_1799_ = lean_box(v___x_1772_);
v___x_1800_ = lean_box(v___x_1791_);
lean_inc(v_i_1762_);
lean_inc_ref(v_types_1759_);
lean_inc_ref(v___x_1787_);
v___f_1801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1801_, 0, v___x_1787_);
lean_closure_set(v___f_1801_, 1, v___x_1768_);
lean_closure_set(v___f_1801_, 2, v_types_1759_);
lean_closure_set(v___f_1801_, 3, v_i_1762_);
lean_closure_set(v___f_1801_, 4, v___x_1798_);
lean_closure_set(v___f_1801_, 5, v___x_1799_);
lean_closure_set(v___f_1801_, 6, v___x_1800_);
v_dummy_1802_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
lean_inc(v_nargs_1797_);
v___x_1803_ = lean_mk_array(v_nargs_1797_, v_dummy_1802_);
v___x_1804_ = lean_nat_sub(v_nargs_1797_, v___x_1770_);
lean_dec(v_nargs_1797_);
lean_inc(v_a_1780_);
v___x_1805_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1780_, v___x_1803_, v___x_1804_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_array_get_borrowed(v___x_1768_, v___x_1805_, v___x_1806_);
lean_inc(v___x_1807_);
v___x_1808_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1796_, v___x_1807_, v___f_1801_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = l_Lean_Core_mkFreshUserName(v___x_1794_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = lean_box(v___x_1790_);
v___x_1813_ = lean_box(v___x_1772_);
v___x_1814_ = lean_box(v___x_1791_);
v___f_1815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1815_, 0, v_i_1762_);
lean_closure_set(v___f_1815_, 1, v___x_1770_);
lean_closure_set(v___f_1815_, 2, v_types_1759_);
lean_closure_set(v___f_1815_, 3, v_u_1760_);
lean_closure_set(v___f_1815_, 4, v___x_1787_);
lean_closure_set(v___f_1815_, 5, v___x_1812_);
lean_closure_set(v___f_1815_, 6, v___x_1813_);
lean_closure_set(v___f_1815_, 7, v___x_1814_);
v___x_1816_ = lean_array_get(v___x_1768_, v___x_1805_, v___x_1770_);
v___x_1817_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1811_, v___x_1816_, v___f_1815_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1834_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1834_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1834_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1822_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
v___x_1823_ = l_Lean_Expr_getAppFn(v_a_1780_);
lean_dec(v_a_1780_);
v___x_1824_ = l_Lean_Expr_constLevels_x21(v___x_1823_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1786_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_mkConst(v___x_1822_, v___x_1825_);
v___x_1827_ = l_Lean_mkAppN(v___x_1826_, v___x_1805_);
lean_dec_ref(v___x_1805_);
v___x_1828_ = l_Lean_Expr_app___override(v___x_1827_, v_a_1793_);
v___x_1829_ = l_Lean_Expr_app___override(v___x_1828_, v_x_1761_);
v___x_1830_ = l_Lean_mkAppB(v___x_1829_, v_a_1809_, v_a_1818_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1830_);
v___x_1832_ = v___x_1820_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
lean_dec(v_a_1809_);
lean_dec_ref(v___x_1805_);
lean_dec(v_a_1793_);
lean_dec(v___x_1786_);
lean_dec(v_a_1780_);
lean_dec_ref(v_x_1761_);
return v___x_1817_;
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_a_1809_);
lean_dec_ref(v___x_1805_);
lean_dec(v_a_1793_);
lean_dec_ref(v___x_1787_);
lean_dec(v___x_1786_);
lean_dec(v_a_1780_);
lean_dec(v_i_1762_);
lean_dec_ref(v_x_1761_);
lean_dec(v_u_1760_);
lean_dec_ref(v_types_1759_);
v_a_1835_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1810_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1810_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_dec_ref(v___x_1805_);
lean_dec(v_a_1793_);
lean_dec_ref(v___x_1787_);
lean_dec(v___x_1786_);
lean_dec(v_a_1780_);
lean_dec(v_i_1762_);
lean_dec_ref(v_x_1761_);
lean_dec(v_u_1760_);
lean_dec_ref(v_types_1759_);
return v___x_1808_;
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_a_1793_);
lean_dec_ref(v___x_1787_);
lean_dec(v___x_1786_);
lean_dec(v_a_1780_);
lean_dec(v_i_1762_);
lean_dec_ref(v_x_1761_);
lean_dec(v_u_1760_);
lean_dec_ref(v_types_1759_);
v_a_1843_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1795_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1795_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_dec_ref(v___x_1787_);
lean_dec(v___x_1786_);
lean_dec(v_a_1780_);
lean_dec(v_i_1762_);
lean_dec_ref(v_x_1761_);
lean_dec(v_u_1760_);
lean_dec_ref(v_types_1759_);
return v___x_1792_;
}
}
}
else
{
lean_dec(v_i_1762_);
lean_dec_ref(v_x_1761_);
lean_dec(v_u_1760_);
lean_dec_ref(v_types_1759_);
return v___x_1779_;
}
}
else
{
lean_dec(v_i_1762_);
lean_dec_ref(v_x_1761_);
lean_dec(v_u_1760_);
lean_dec_ref(v_types_1759_);
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object* v_i_1851_, lean_object* v___x_1852_, lean_object* v_types_1853_, lean_object* v_u_1854_, lean_object* v___x_1855_, uint8_t v___x_1856_, uint8_t v___x_1857_, uint8_t v___x_1858_, lean_object* v_x_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_nat_add(v_i_1851_, v___x_1852_);
lean_inc_ref(v_x_1859_);
v___x_1866_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1853_, v_u_1854_, v_x_1859_, v___x_1865_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___x_1868_ = lean_array_push(v___x_1855_, v_x_1859_);
v___x_1869_ = l_Lean_Meta_mkLambdaFVars(v___x_1868_, v_a_1867_, v___x_1856_, v___x_1857_, v___x_1856_, v___x_1857_, v___x_1858_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec_ref(v___x_1868_);
return v___x_1869_;
}
else
{
lean_dec_ref(v_x_1859_);
lean_dec_ref(v___x_1855_);
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object* v_types_1870_, lean_object* v_u_1871_, lean_object* v_x_1872_, lean_object* v_i_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1870_, v_u_1871_, v_x_1872_, v_i_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object* v_x_1880_, lean_object* v_body_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Meta_getLevel(v_body_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object* v_x_1888_, lean_object* v_body_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1888_, v_body_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec_ref(v_x_1888_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object* v_types_1897_, lean_object* v_x_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___f_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; 
v___f_1904_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0));
v___x_1905_ = l_Lean_instInhabitedExpr;
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_array_get_borrowed(v___x_1905_, v_types_1897_, v___x_1906_);
v___x_1908_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1909_ = 0;
lean_inc(v___x_1907_);
v___x_1910_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_1907_, v___x_1908_, v___f_1904_, v___x_1909_, v___x_1909_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1897_, v_a_1911_, v_x_1898_, v___x_1906_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_1912_;
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_x_1898_);
lean_dec_ref(v_types_1897_);
v_a_1913_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1910_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1910_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object* v_types_1921_, lean_object* v_x_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1921_, v_x_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object* v_a_1929_, lean_object* v___x_1930_, uint8_t v___x_1931_, lean_object* v_x_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; 
lean_inc_ref(v_x_1932_);
v___x_1938_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_a_1929_, v_x_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1940_ = lean_mk_empty_array_with_capacity(v___x_1930_);
v___x_1941_ = lean_array_push(v___x_1940_, v_x_1932_);
v___x_1942_ = 1;
v___x_1943_ = 1;
v___x_1944_ = l_Lean_Meta_mkForallFVars(v___x_1941_, v_a_1939_, v___x_1931_, v___x_1942_, v___x_1942_, v___x_1943_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec_ref(v___x_1941_);
return v___x_1944_;
}
else
{
lean_dec_ref(v_x_1932_);
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object* v_a_1945_, lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v_x_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
uint8_t v___x_1816__boxed_1954_; lean_object* v_res_1955_; 
v___x_1816__boxed_1954_ = lean_unbox(v___x_1947_);
v_res_1955_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1945_, v___x_1946_, v___x_1816__boxed_1954_, v_x_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___x_1946_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t v_sz_1956_, size_t v_i_1957_, lean_object* v_bs_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_usize_dec_lt(v_i_1957_, v_sz_1956_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_bs_1958_);
return v___x_1965_;
}
else
{
lean_object* v_v_1966_; lean_object* v___x_1967_; 
v_v_1966_ = lean_array_uget_borrowed(v_bs_1958_, v_i_1957_);
lean_inc(v_v_1966_);
v___x_1967_ = l_Lean_Meta_whnfForall(v_v_1966_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; lean_object* v_bs_x27_1970_; size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = lean_unsigned_to_nat(0u);
v_bs_x27_1970_ = lean_array_uset(v_bs_1958_, v_i_1957_, v___x_1969_);
v___x_1971_ = ((size_t)1ULL);
v___x_1972_ = lean_usize_add(v_i_1957_, v___x_1971_);
v___x_1973_ = lean_array_uset(v_bs_x27_1970_, v_i_1957_, v_a_1968_);
v_i_1957_ = v___x_1972_;
v_bs_1958_ = v___x_1973_;
goto _start;
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_bs_1958_);
v_a_1975_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1967_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1967_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object* v_sz_1983_, lean_object* v_i_1984_, lean_object* v_bs_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
size_t v_sz_boxed_1991_; size_t v_i_boxed_1992_; lean_object* v_res_1993_; 
v_sz_boxed_1991_ = lean_unbox_usize(v_sz_1983_);
lean_dec(v_sz_1983_);
v_i_boxed_1992_ = lean_unbox_usize(v_i_1984_);
lean_dec(v_i_1984_);
v_res_1993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_1991_, v_i_boxed_1992_, v_bs_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
return v_res_1993_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0));
v___x_1996_ = l_Lean_stringToMessageData(v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object* v_as_1997_, size_t v_i_1998_, size_t v_stop_1999_, lean_object* v_b_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_a_2007_; uint8_t v___x_2011_; 
v___x_2011_ = lean_usize_dec_eq(v_i_1998_, v_stop_1999_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = lean_array_uget_borrowed(v_as_1997_, v_i_1998_);
v___x_2013_ = l_Lean_Expr_isForall(v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2014_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
lean_inc(v___x_2012_);
v___x_2015_ = l_Lean_MessageData_ofExpr(v___x_2012_);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2016_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v_a_2007_ = v_a_2018_;
goto v___jp_2006_;
}
else
{
return v___x_2017_;
}
}
else
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_box(0);
v_a_2007_ = v___x_2019_;
goto v___jp_2006_;
}
}
else
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_b_2000_);
return v___x_2020_;
}
v___jp_2006_:
{
size_t v___x_2008_; size_t v___x_2009_; 
v___x_2008_ = ((size_t)1ULL);
v___x_2009_ = lean_usize_add(v_i_1998_, v___x_2008_);
v_i_1998_ = v___x_2009_;
v_b_2000_ = v_a_2007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object* v_as_2021_, lean_object* v_i_2022_, lean_object* v_stop_2023_, lean_object* v_b_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
size_t v_i_boxed_2030_; size_t v_stop_boxed_2031_; lean_object* v_res_2032_; 
v_i_boxed_2030_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_stop_boxed_2031_ = lean_unbox_usize(v_stop_2023_);
lean_dec(v_stop_2023_);
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_2021_, v_i_boxed_2030_, v_stop_boxed_2031_, v_b_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v_as_2021_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t v_sz_2033_, size_t v_i_2034_, lean_object* v_bs_2035_){
_start:
{
uint8_t v___x_2036_; 
v___x_2036_ = lean_usize_dec_lt(v_i_2034_, v_sz_2033_);
if (v___x_2036_ == 0)
{
return v_bs_2035_;
}
else
{
lean_object* v_v_2037_; lean_object* v___x_2038_; lean_object* v_bs_x27_2039_; lean_object* v___x_2040_; size_t v___x_2041_; size_t v___x_2042_; lean_object* v___x_2043_; 
v_v_2037_ = lean_array_uget(v_bs_2035_, v_i_2034_);
v___x_2038_ = lean_unsigned_to_nat(0u);
v_bs_x27_2039_ = lean_array_uset(v_bs_2035_, v_i_2034_, v___x_2038_);
v___x_2040_ = l_Lean_Expr_bindingDomain_x21(v_v_2037_);
lean_dec(v_v_2037_);
v___x_2041_ = ((size_t)1ULL);
v___x_2042_ = lean_usize_add(v_i_2034_, v___x_2041_);
v___x_2043_ = lean_array_uset(v_bs_x27_2039_, v_i_2034_, v___x_2040_);
v_i_2034_ = v___x_2042_;
v_bs_2035_ = v___x_2043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object* v_sz_2045_, lean_object* v_i_2046_, lean_object* v_bs_2047_){
_start:
{
size_t v_sz_boxed_2048_; size_t v_i_boxed_2049_; lean_object* v_res_2050_; 
v_sz_boxed_2048_ = lean_unbox_usize(v_sz_2045_);
lean_dec(v_sz_2045_);
v_i_boxed_2049_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_2048_, v_i_boxed_2049_, v_bs_2047_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object* v_types_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_array_get_size(v_types_2051_);
v___x_2058_ = lean_unsigned_to_nat(1u);
v___x_2059_ = lean_nat_dec_eq(v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
size_t v_sz_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v_sz_2060_ = lean_array_size(v_types_2051_);
v___x_2061_ = ((size_t)0ULL);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2060_, v___x_2061_, v_types_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; lean_object* v___f_2065_; lean_object* v___y_2084_; lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc_n(v_a_2063_, 2);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = lean_box(v___x_2059_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2065_, 0, v_a_2063_);
lean_closure_set(v___f_2065_, 1, v___x_2058_);
lean_closure_set(v___f_2065_, 2, v___x_2064_);
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = lean_array_get_size(v_a_2063_);
v___x_2095_ = lean_nat_dec_lt(v___x_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
goto v___jp_2066_;
}
else
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_nat_dec_le(v___x_2094_, v___x_2094_);
if (v___x_2097_ == 0)
{
if (v___x_2095_ == 0)
{
goto v___jp_2066_;
}
else
{
size_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_usize_of_nat(v___x_2094_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2063_, v___x_2061_, v___x_2098_, v___x_2096_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
v___y_2084_ = v___x_2099_;
goto v___jp_2083_;
}
}
else
{
size_t v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_usize_of_nat(v___x_2094_);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2063_, v___x_2061_, v___x_2100_, v___x_2096_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
v___y_2084_ = v___x_2101_;
goto v___jp_2083_;
}
}
v___jp_2066_:
{
size_t v_sz_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v_sz_2067_ = lean_array_size(v_a_2063_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_2067_, v___x_2061_, v_a_2063_);
v___x_2069_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2068_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2072_ = l_Lean_Core_mkFreshUserName(v___x_2071_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2073_, v_a_2070_, v___f_2065_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
return v___x_2074_;
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2070_);
lean_dec_ref(v___f_2065_);
v_a_2075_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2072_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2072_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_dec_ref(v___f_2065_);
return v___x_2069_;
}
}
v___jp_2083_:
{
if (lean_obj_tag(v___y_2084_) == 0)
{
lean_dec_ref_known(v___y_2084_, 1);
goto v___jp_2066_;
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v___f_2065_);
lean_dec(v_a_2063_);
v_a_2085_ = lean_ctor_get(v___y_2084_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___y_2084_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___y_2084_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___y_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
v_a_2102_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2062_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2062_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2110_ = l_Lean_instInhabitedExpr;
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = lean_array_get(v___x_2110_, v_types_2051_, v___x_2111_);
lean_dec_ref(v_types_2051_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object* v_types_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2120_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0));
v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2));
v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object* v___x_2127_, lean_object* v_as_2128_, size_t v_i_2129_, size_t v_stop_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_a_2138_; uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_eq(v_i_2129_, v_stop_2130_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_array_uget_borrowed(v_as_2128_, v_i_2129_);
lean_inc_ref(v___x_2127_);
lean_inc(v___x_2143_);
v___x_2144_ = l_Lean_Meta_isExprDefEq(v___x_2143_, v___x_2127_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; uint8_t v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = lean_unbox(v_a_2145_);
lean_dec(v_a_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2147_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
lean_inc(v___x_2143_);
v___x_2148_ = l_Lean_MessageData_ofExpr(v___x_2143_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
v___x_2151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
lean_inc_ref(v___x_2127_);
v___x_2152_ = l_Lean_MessageData_ofExpr(v___x_2127_);
v___x_2153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2153_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v_a_2138_ = v_a_2155_;
goto v___jp_2137_;
}
else
{
lean_dec_ref(v___x_2127_);
return v___x_2154_;
}
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_box(0);
v_a_2138_ = v___x_2156_;
goto v___jp_2137_;
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v___x_2127_);
v_a_2157_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2144_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2144_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v___x_2165_; 
lean_dec_ref(v___x_2127_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_b_2131_);
return v___x_2165_;
}
v___jp_2137_:
{
size_t v___x_2139_; size_t v___x_2140_; 
v___x_2139_ = ((size_t)1ULL);
v___x_2140_ = lean_usize_add(v_i_2129_, v___x_2139_);
v_i_2129_ = v___x_2140_;
v_b_2131_ = v_a_2138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object* v___x_2166_, lean_object* v_as_2167_, lean_object* v_i_2168_, lean_object* v_stop_2169_, lean_object* v_b_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
size_t v_i_boxed_2176_; size_t v_stop_boxed_2177_; lean_object* v_res_2178_; 
v_i_boxed_2176_ = lean_unbox_usize(v_i_2168_);
lean_dec(v_i_2168_);
v_stop_boxed_2177_ = lean_unbox_usize(v_stop_2169_);
lean_dec(v_stop_2169_);
v_res_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2166_, v_as_2167_, v_i_boxed_2176_, v_stop_boxed_2177_, v_b_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec_ref(v_as_2167_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t v_sz_2179_, size_t v_i_2180_, lean_object* v_bs_2181_){
_start:
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_usize_dec_lt(v_i_2180_, v_sz_2179_);
if (v___x_2182_ == 0)
{
return v_bs_2181_;
}
else
{
lean_object* v_v_2183_; lean_object* v___x_2184_; lean_object* v_bs_x27_2185_; lean_object* v___x_2186_; size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v_v_2183_ = lean_array_uget(v_bs_2181_, v_i_2180_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v_bs_x27_2185_ = lean_array_uset(v_bs_2181_, v_i_2180_, v___x_2184_);
v___x_2186_ = l_Lean_Expr_bindingBody_x21(v_v_2183_);
lean_dec(v_v_2183_);
v___x_2187_ = ((size_t)1ULL);
v___x_2188_ = lean_usize_add(v_i_2180_, v___x_2187_);
v___x_2189_ = lean_array_uset(v_bs_x27_2185_, v_i_2180_, v___x_2186_);
v_i_2180_ = v___x_2188_;
v_bs_2181_ = v___x_2189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object* v_sz_2191_, lean_object* v_i_2192_, lean_object* v_bs_2193_){
_start:
{
size_t v_sz_boxed_2194_; size_t v_i_boxed_2195_; lean_object* v_res_2196_; 
v_sz_boxed_2194_ = lean_unbox_usize(v_sz_2191_);
lean_dec(v_sz_2191_);
v_i_boxed_2195_ = lean_unbox_usize(v_i_2192_);
lean_dec(v_i_2192_);
v_res_2196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_2194_, v_i_boxed_2195_, v_bs_2193_);
return v_res_2196_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object* v_as_2200_, size_t v_i_2201_, size_t v_stop_2202_, lean_object* v_b_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_a_2210_; uint8_t v___x_2214_; 
v___x_2214_ = lean_usize_dec_eq(v_i_2201_, v_stop_2202_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_array_uget_borrowed(v_as_2200_, v_i_2201_);
v___x_2216_ = l_Lean_Expr_isArrow(v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2217_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
lean_inc(v___x_2215_);
v___x_2218_ = l_Lean_MessageData_ofExpr(v___x_2215_);
v___x_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2217_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2219_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v_a_2210_ = v_a_2221_;
goto v___jp_2209_;
}
else
{
return v___x_2220_;
}
}
else
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_box(0);
v_a_2210_ = v___x_2222_;
goto v___jp_2209_;
}
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_b_2203_);
return v___x_2223_;
}
v___jp_2209_:
{
size_t v___x_2211_; size_t v___x_2212_; 
v___x_2211_ = ((size_t)1ULL);
v___x_2212_ = lean_usize_add(v_i_2201_, v___x_2211_);
v_i_2201_ = v___x_2212_;
v_b_2203_ = v_a_2210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object* v_as_2224_, lean_object* v_i_2225_, lean_object* v_stop_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
size_t v_i_boxed_2233_; size_t v_stop_boxed_2234_; lean_object* v_res_2235_; 
v_i_boxed_2233_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_stop_boxed_2234_ = lean_unbox_usize(v_stop_2226_);
lean_dec(v_stop_2226_);
v_res_2235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2224_, v_i_boxed_2233_, v_stop_boxed_2234_, v_b_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_as_2224_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object* v_types_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
size_t v_sz_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v_sz_2242_ = lean_array_size(v_types_2236_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2242_, v___x_2243_, v_types_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___y_2249_; size_t v___y_2250_; lean_object* v___y_2257_; size_t v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2285_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v___x_2246_ = l_Lean_instInhabitedExpr;
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2294_ = lean_array_get_size(v_a_2245_);
v___x_2295_ = lean_nat_dec_lt(v___x_2247_, v___x_2294_);
if (v___x_2295_ == 0)
{
goto v___jp_2268_;
}
else
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_nat_dec_le(v___x_2294_, v___x_2294_);
if (v___x_2297_ == 0)
{
if (v___x_2295_ == 0)
{
goto v___jp_2268_;
}
else
{
size_t v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_usize_of_nat(v___x_2294_);
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2245_, v___x_2243_, v___x_2298_, v___x_2296_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
v___y_2285_ = v___x_2299_;
goto v___jp_2284_;
}
}
else
{
size_t v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = lean_usize_of_nat(v___x_2294_);
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2245_, v___x_2243_, v___x_2300_, v___x_2296_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
v___y_2285_ = v___x_2301_;
goto v___jp_2284_;
}
}
v___jp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_2250_, v___x_2243_, v_a_2245_);
v___x_2252_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2251_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2254_ = lean_array_get(v___x_2246_, v___y_2249_, v___x_2247_);
lean_dec_ref(v___y_2249_);
v___x_2255_ = l_Lean_mkArrow(v_a_2253_, v___x_2254_, v_a_2239_, v_a_2240_);
return v___x_2255_;
}
else
{
lean_dec_ref(v___y_2249_);
return v___x_2252_;
}
}
v___jp_2256_:
{
if (lean_obj_tag(v___y_2259_) == 0)
{
lean_dec_ref_known(v___y_2259_, 1);
v___y_2249_ = v___y_2257_;
v___y_2250_ = v___y_2258_;
goto v___jp_2248_;
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec_ref(v___y_2257_);
lean_dec(v_a_2245_);
v_a_2260_ = lean_ctor_get(v___y_2259_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___y_2259_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___y_2259_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___y_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
v___jp_2268_:
{
size_t v_sz_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_sz_2269_ = lean_array_size(v_a_2245_);
lean_inc(v_a_2245_);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2269_, v___x_2243_, v_a_2245_);
v___x_2271_ = lean_array_get_size(v___x_2270_);
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_sub(v___x_2271_, v___x_2272_);
v___x_2274_ = lean_array_get(v___x_2246_, v___x_2270_, v___x_2273_);
lean_dec(v___x_2273_);
lean_inc_ref(v___x_2270_);
v___x_2275_ = lean_array_pop(v___x_2270_);
v___x_2276_ = lean_array_get_size(v___x_2275_);
v___x_2277_ = lean_nat_dec_lt(v___x_2247_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_dec_ref(v___x_2275_);
lean_dec(v___x_2274_);
v___y_2249_ = v___x_2270_;
v___y_2250_ = v_sz_2269_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2278_ = lean_box(0);
v___x_2279_ = lean_nat_dec_le(v___x_2276_, v___x_2276_);
if (v___x_2279_ == 0)
{
if (v___x_2277_ == 0)
{
lean_dec_ref(v___x_2275_);
lean_dec(v___x_2274_);
v___y_2249_ = v___x_2270_;
v___y_2250_ = v_sz_2269_;
goto v___jp_2248_;
}
else
{
size_t v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_usize_of_nat(v___x_2276_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2274_, v___x_2275_, v___x_2243_, v___x_2280_, v___x_2278_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec_ref(v___x_2275_);
v___y_2257_ = v___x_2270_;
v___y_2258_ = v_sz_2269_;
v___y_2259_ = v___x_2281_;
goto v___jp_2256_;
}
}
else
{
size_t v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_usize_of_nat(v___x_2276_);
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2274_, v___x_2275_, v___x_2243_, v___x_2282_, v___x_2278_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec_ref(v___x_2275_);
v___y_2257_ = v___x_2270_;
v___y_2258_ = v_sz_2269_;
v___y_2259_ = v___x_2283_;
goto v___jp_2256_;
}
}
}
v___jp_2284_:
{
if (lean_obj_tag(v___y_2285_) == 0)
{
lean_dec_ref_known(v___y_2285_, 1);
goto v___jp_2268_;
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_a_2245_);
v_a_2286_ = lean_ctor_get(v___y_2285_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___y_2285_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___y_2285_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___y_2285_);
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
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_a_2302_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2244_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2244_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object* v_types_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
return v_res_2316_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object* v___x_2323_, lean_object* v___x_2324_, lean_object* v_arg_2325_, lean_object* v_arg_2326_, lean_object* v___x_2327_, lean_object* v_a_2328_, lean_object* v_tail_2329_, lean_object* v___x_2330_, lean_object* v___x_2331_, lean_object* v___x_2332_, lean_object* v_y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
uint8_t v___x_2349__boxed_2339_; uint8_t v___x_2350__boxed_2340_; uint8_t v___x_2351__boxed_2341_; lean_object* v_res_2342_; 
v___x_2349__boxed_2339_ = lean_unbox(v___x_2330_);
v___x_2350__boxed_2340_ = lean_unbox(v___x_2331_);
v___x_2351__boxed_2341_ = lean_unbox(v___x_2332_);
v_res_2342_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v___x_2323_, v___x_2324_, v_arg_2325_, v_arg_2326_, v___x_2327_, v_a_2328_, v_tail_2329_, v___x_2349__boxed_2339_, v___x_2350__boxed_2340_, v___x_2351__boxed_2341_, v_y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object* v_x_2343_, lean_object* v_codomain_2344_, lean_object* v_alts_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
if (lean_obj_tag(v_alts_2345_) == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
lean_dec_ref(v_codomain_2344_);
lean_dec_ref(v_x_2343_);
v___x_2351_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
v___x_2352_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2351_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2352_;
}
else
{
lean_object* v_tail_2353_; 
v_tail_2353_ = lean_ctor_get(v_alts_2345_, 1);
if (lean_obj_tag(v_tail_2353_) == 0)
{
lean_object* v_head_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec_ref(v_codomain_2344_);
v_head_2354_ = lean_ctor_get(v_alts_2345_, 0);
lean_inc(v_head_2354_);
lean_dec_ref_known(v_alts_2345_, 2);
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_2357_ = lean_array_push(v___x_2356_, v_x_2343_);
v___x_2358_ = l_Lean_Expr_beta(v_head_2354_, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
else
{
lean_object* v_head_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2445_; 
lean_inc(v_tail_2353_);
v_head_2360_ = lean_ctor_get(v_alts_2345_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_alts_2345_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; 
v_unused_2446_ = lean_ctor_get(v_alts_2345_, 1);
lean_dec(v_unused_2446_);
v___x_2362_ = v_alts_2345_;
v_isShared_2363_ = v_isSharedCheck_2445_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_head_2360_);
lean_dec(v_alts_2345_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2445_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; 
lean_inc(v_a_2349_);
lean_inc_ref(v_a_2348_);
lean_inc(v_a_2347_);
lean_inc_ref(v_a_2346_);
lean_inc_ref(v_x_2343_);
v___x_2364_ = lean_infer_type(v_x_2343_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc_n(v_a_2365_, 2);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2365_, v_a_2347_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2377_ = l_Lean_Expr_cleanupAnnotations(v_a_2367_);
v___x_2378_ = l_Lean_Expr_isApp(v___x_2377_);
if (v___x_2378_ == 0)
{
lean_dec_ref(v___x_2377_);
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec(v_tail_2353_);
lean_dec_ref(v_codomain_2344_);
lean_dec_ref(v_x_2343_);
v___y_2369_ = v_a_2346_;
v___y_2370_ = v_a_2347_;
v___y_2371_ = v_a_2348_;
v___y_2372_ = v_a_2349_;
goto v___jp_2368_;
}
else
{
lean_object* v_arg_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_arg_2379_ = lean_ctor_get(v___x_2377_, 1);
lean_inc_ref(v_arg_2379_);
v___x_2380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2377_);
v___x_2381_ = l_Lean_Expr_isApp(v___x_2380_);
if (v___x_2381_ == 0)
{
lean_dec_ref(v___x_2380_);
lean_dec_ref(v_arg_2379_);
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec(v_tail_2353_);
lean_dec_ref(v_codomain_2344_);
lean_dec_ref(v_x_2343_);
v___y_2369_ = v_a_2346_;
v___y_2370_ = v_a_2347_;
v___y_2371_ = v_a_2348_;
v___y_2372_ = v_a_2349_;
goto v___jp_2368_;
}
else
{
lean_object* v_arg_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v_arg_2382_ = lean_ctor_get(v___x_2380_, 1);
lean_inc_ref(v_arg_2382_);
v___x_2383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2380_);
v___x_2384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0));
v___x_2385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_2386_ = l_Lean_Expr_isConstOf(v___x_2383_, v___x_2385_);
lean_dec_ref(v___x_2383_);
if (v___x_2386_ == 0)
{
lean_dec_ref(v_arg_2382_);
lean_dec_ref(v_arg_2379_);
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec(v_tail_2353_);
lean_dec_ref(v_codomain_2344_);
lean_dec_ref(v_x_2343_);
v___y_2369_ = v_a_2346_;
v___y_2370_ = v_a_2347_;
v___y_2371_ = v_a_2348_;
v___y_2372_ = v_a_2349_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2387_; 
lean_inc_ref(v_codomain_2344_);
v___x_2387_ = l_Lean_Meta_getLevel(v_codomain_2344_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = lean_mk_empty_array_with_capacity(v___x_2389_);
lean_inc_ref(v_x_2343_);
lean_inc_ref(v___x_2390_);
v___x_2391_ = lean_array_push(v___x_2390_, v_x_2343_);
v___x_2392_ = 0;
v___x_2393_ = 1;
v___x_2394_ = l_Lean_Meta_mkLambdaFVars(v___x_2391_, v_codomain_2344_, v___x_2392_, v___x_2386_, v___x_2392_, v___x_2386_, v___x_2393_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec_ref(v___x_2391_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2436_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2436_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2436_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v_alt_u2082_2402_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; 
v___x_2399_ = l_Lean_Expr_getAppFn(v_a_2365_);
lean_dec(v_a_2365_);
v___x_2400_ = l_Lean_Expr_constLevels_x21(v___x_2399_);
lean_dec_ref(v___x_2399_);
v___x_2412_ = lean_box(v___x_2392_);
v___x_2413_ = lean_box(v___x_2386_);
v___x_2414_ = lean_box(v___x_2393_);
lean_inc(v_tail_2353_);
lean_inc(v_a_2395_);
lean_inc_ref(v_arg_2379_);
lean_inc_ref(v_arg_2382_);
lean_inc(v___x_2400_);
v___f_2415_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2415_, 0, v___x_2384_);
lean_closure_set(v___f_2415_, 1, v___x_2400_);
lean_closure_set(v___f_2415_, 2, v_arg_2382_);
lean_closure_set(v___f_2415_, 3, v_arg_2379_);
lean_closure_set(v___f_2415_, 4, v___x_2390_);
lean_closure_set(v___f_2415_, 5, v_a_2395_);
lean_closure_set(v___f_2415_, 6, v_tail_2353_);
lean_closure_set(v___f_2415_, 7, v___x_2412_);
lean_closure_set(v___f_2415_, 8, v___x_2413_);
lean_closure_set(v___f_2415_, 9, v___x_2414_);
if (lean_obj_tag(v_tail_2353_) == 1)
{
lean_object* v_tail_2434_; 
v_tail_2434_ = lean_ctor_get(v_tail_2353_, 1);
if (lean_obj_tag(v_tail_2434_) == 0)
{
lean_object* v_head_2435_; 
lean_dec_ref(v___f_2415_);
v_head_2435_ = lean_ctor_get(v_tail_2353_, 0);
lean_inc(v_head_2435_);
lean_dec_ref_known(v_tail_2353_, 2);
v_alt_u2082_2402_ = v_head_2435_;
goto v___jp_2401_;
}
else
{
lean_dec_ref_known(v_tail_2353_, 2);
v___y_2417_ = v_a_2346_;
v___y_2418_ = v_a_2347_;
v___y_2419_ = v_a_2348_;
v___y_2420_ = v_a_2349_;
goto v___jp_2416_;
}
}
else
{
lean_dec(v_tail_2353_);
v___y_2417_ = v_a_2346_;
v___y_2418_ = v_a_2347_;
v___y_2419_ = v_a_2348_;
v___y_2420_ = v_a_2349_;
goto v___jp_2416_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v___x_2400_);
lean_ctor_set(v___x_2362_, 0, v_a_2388_);
v___x_2405_ = v___x_2362_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2388_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___x_2400_);
v___x_2405_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2406_ = l_Lean_Expr_const___override(v___x_2403_, v___x_2405_);
v___x_2407_ = l_Lean_mkApp6(v___x_2406_, v_arg_2382_, v_arg_2379_, v_a_2395_, v_x_2343_, v_head_2360_, v_alt_u2082_2402_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2407_);
v___x_2409_ = v___x_2397_;
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
v___jp_2416_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_2422_ = l_Lean_Core_mkFreshUserName(v___x_2421_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
lean_inc_ref(v_arg_2379_);
v___x_2424_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2423_, v_arg_2379_, v___f_2415_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v_alt_u2082_2402_ = v_a_2425_;
goto v___jp_2401_;
}
else
{
lean_dec(v___x_2400_);
lean_del_object(v___x_2397_);
lean_dec(v_a_2395_);
lean_dec(v_a_2388_);
lean_dec_ref(v_arg_2382_);
lean_dec_ref(v_arg_2379_);
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec_ref(v_x_2343_);
return v___x_2424_;
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v___f_2415_);
lean_dec(v___x_2400_);
lean_del_object(v___x_2397_);
lean_dec(v_a_2395_);
lean_dec(v_a_2388_);
lean_dec_ref(v_arg_2382_);
lean_dec_ref(v_arg_2379_);
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec_ref(v_x_2343_);
v_a_2426_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2422_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2422_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2390_);
lean_dec(v_a_2388_);
lean_dec_ref(v_arg_2382_);
lean_dec_ref(v_arg_2379_);
lean_dec(v_a_2365_);
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec(v_tail_2353_);
lean_dec_ref(v_x_2343_);
return v___x_2394_;
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v_arg_2382_);
lean_dec_ref(v_arg_2379_);
lean_dec(v_a_2365_);
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec(v_tail_2353_);
lean_dec_ref(v_codomain_2344_);
lean_dec_ref(v_x_2343_);
v_a_2437_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2387_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2387_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
}
v___jp_2368_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2373_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
v___x_2374_ = l_Lean_MessageData_ofExpr(v_a_2365_);
v___x_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2375_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2376_;
}
}
else
{
lean_dec(v_a_2365_);
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec(v_tail_2353_);
lean_dec_ref(v_codomain_2344_);
lean_dec_ref(v_x_2343_);
return v___x_2366_;
}
}
else
{
lean_del_object(v___x_2362_);
lean_dec(v_head_2360_);
lean_dec(v_tail_2353_);
lean_dec_ref(v_codomain_2344_);
lean_dec_ref(v_x_2343_);
return v___x_2364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object* v___x_2447_, lean_object* v___x_2448_, lean_object* v_arg_2449_, lean_object* v_arg_2450_, lean_object* v___x_2451_, lean_object* v_a_2452_, lean_object* v_tail_2453_, uint8_t v___x_2454_, uint8_t v___x_2455_, uint8_t v___x_2456_, lean_object* v_y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2463_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3));
v___x_2464_ = l_Lean_Name_mkStr2(v___x_2447_, v___x_2463_);
v___x_2465_ = l_Lean_Expr_const___override(v___x_2464_, v___x_2448_);
lean_inc_ref_n(v_y_2457_, 2);
v___x_2466_ = l_Lean_mkApp3(v___x_2465_, v_arg_2449_, v_arg_2450_, v_y_2457_);
lean_inc_ref(v___x_2451_);
v___x_2467_ = lean_array_push(v___x_2451_, v___x_2466_);
v___x_2468_ = l_Lean_Expr_beta(v_a_2452_, v___x_2467_);
v___x_2469_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_y_2457_, v___x_2468_, v_tail_2453_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2471_ = lean_array_push(v___x_2451_, v_y_2457_);
v___x_2472_ = l_Lean_Meta_mkLambdaFVars(v___x_2471_, v_a_2470_, v___x_2454_, v___x_2455_, v___x_2454_, v___x_2455_, v___x_2456_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec_ref(v___x_2471_);
return v___x_2472_;
}
else
{
lean_dec_ref(v_y_2457_);
lean_dec_ref(v___x_2451_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object* v_x_2473_, lean_object* v_codomain_2474_, lean_object* v_alts_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2473_, v_codomain_2474_, v_alts_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
return v_res_2481_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2483_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2484_ = lean_unsigned_to_nat(21u);
v___x_2485_ = lean_unsigned_to_nat(417u);
v___x_2486_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0));
v___x_2487_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2488_ = l_mkPanicMessageWithDecl(v___x_2487_, v___x_2486_, v___x_2485_, v___x_2484_, v___x_2483_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object* v___x_2489_, lean_object* v_es_2490_, lean_object* v_xs_2491_, lean_object* v_codomain_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = lean_array_get_size(v_xs_2491_);
v___x_2499_ = lean_nat_dec_eq(v___x_2498_, v___x_2489_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec_ref(v_codomain_2492_);
lean_dec_ref(v_es_2490_);
v___x_2500_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1);
v___x_2501_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2500_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = lean_array_fget_borrowed(v_xs_2491_, v___x_2502_);
v___x_2504_ = lean_array_to_list(v_es_2490_);
lean_inc(v___x_2503_);
v___x_2505_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2503_, v_codomain_2492_, v___x_2504_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = lean_mk_empty_array_with_capacity(v___x_2489_);
lean_inc(v___x_2503_);
v___x_2508_ = lean_array_push(v___x_2507_, v___x_2503_);
v___x_2509_ = 0;
v___x_2510_ = 1;
v___x_2511_ = l_Lean_Meta_mkLambdaFVars(v___x_2508_, v_a_2506_, v___x_2509_, v___x_2499_, v___x_2509_, v___x_2499_, v___x_2510_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec_ref(v___x_2508_);
return v___x_2511_;
}
else
{
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(lean_object* v___x_2512_, lean_object* v_es_2513_, lean_object* v_xs_2514_, lean_object* v_codomain_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(v___x_2512_, v_es_2513_, v_xs_2514_, v_codomain_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v_xs_2514_);
lean_dec(v___x_2512_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(lean_object* v_resultType_2522_, lean_object* v_es_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; lean_object* v___f_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2529_ = lean_unsigned_to_nat(1u);
v___f_2530_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2530_, 0, v___x_2529_);
lean_closure_set(v___f_2530_, 1, v_es_2523_);
v___x_2531_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2532_ = 0;
v___x_2533_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_resultType_2522_, v___x_2531_, v___f_2530_, v___x_2532_, v___x_2532_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(lean_object* v_resultType_2534_, lean_object* v_es_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_2534_, v_es_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(size_t v_sz_2542_, size_t v_i_2543_, lean_object* v_bs_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
uint8_t v___x_2550_; 
v___x_2550_ = lean_usize_dec_lt(v_i_2543_, v_sz_2542_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_bs_2544_);
return v___x_2551_;
}
else
{
lean_object* v_v_2552_; lean_object* v___x_2553_; 
v_v_2552_ = lean_array_uget_borrowed(v_bs_2544_, v_i_2543_);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
lean_inc(v_v_2552_);
v___x_2553_ = lean_infer_type(v_v_2552_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; lean_object* v_bs_x27_2556_; size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = lean_unsigned_to_nat(0u);
v_bs_x27_2556_ = lean_array_uset(v_bs_2544_, v_i_2543_, v___x_2555_);
v___x_2557_ = ((size_t)1ULL);
v___x_2558_ = lean_usize_add(v_i_2543_, v___x_2557_);
v___x_2559_ = lean_array_uset(v_bs_x27_2556_, v_i_2543_, v_a_2554_);
v_i_2543_ = v___x_2558_;
v_bs_2544_ = v___x_2559_;
goto _start;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec_ref(v_bs_2544_);
v_a_2561_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2553_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2553_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(lean_object* v_sz_2569_, lean_object* v_i_2570_, lean_object* v_bs_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
size_t v_sz_boxed_2577_; size_t v_i_boxed_2578_; lean_object* v_res_2579_; 
v_sz_boxed_2577_ = lean_unbox_usize(v_sz_2569_);
lean_dec(v_sz_2569_);
v_i_boxed_2578_ = lean_unbox_usize(v_i_2570_);
lean_dec(v_i_2570_);
v_res_2579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_boxed_2577_, v_i_boxed_2578_, v_bs_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry(lean_object* v_es_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
size_t v_sz_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v_sz_2586_ = lean_array_size(v_es_2580_);
v___x_2587_ = ((size_t)0ULL);
lean_inc_ref(v_es_2580_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2586_, v___x_2587_, v_es_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2589_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_a_2591_, v_es_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
return v___x_2592_;
}
else
{
lean_dec_ref(v_es_2580_);
return v___x_2590_;
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v_es_2580_);
v_a_2593_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2588_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2588_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(lean_object* v_es_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_es_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
return v_res_2607_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2609_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2610_ = lean_unsigned_to_nat(21u);
v___x_2611_ = lean_unsigned_to_nat(437u);
v___x_2612_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0));
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2614_ = l_mkPanicMessageWithDecl(v___x_2613_, v___x_2612_, v___x_2611_, v___x_2610_, v___x_2609_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(lean_object* v___x_2615_, lean_object* v_es_2616_, lean_object* v_xs_2617_, lean_object* v_codomain_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2624_ = lean_array_get_size(v_xs_2617_);
v___x_2625_ = lean_nat_dec_eq(v___x_2624_, v___x_2615_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v_codomain_2618_);
lean_dec_ref(v_es_2616_);
v___x_2626_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1);
v___x_2627_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2626_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2627_;
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_array_fget_borrowed(v_xs_2617_, v___x_2628_);
v___x_2630_ = lean_array_to_list(v_es_2616_);
lean_inc(v___x_2629_);
v___x_2631_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2629_, v_codomain_2618_, v___x_2630_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = lean_mk_empty_array_with_capacity(v___x_2615_);
lean_inc(v___x_2629_);
v___x_2634_ = lean_array_push(v___x_2633_, v___x_2629_);
v___x_2635_ = 0;
v___x_2636_ = 1;
v___x_2637_ = l_Lean_Meta_mkLambdaFVars(v___x_2634_, v_a_2632_, v___x_2635_, v___x_2625_, v___x_2635_, v___x_2625_, v___x_2636_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec_ref(v___x_2634_);
return v___x_2637_;
}
else
{
return v___x_2631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object* v___x_2638_, lean_object* v_es_2639_, lean_object* v_xs_2640_, lean_object* v_codomain_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2638_, v_es_2639_, v_xs_2640_, v_codomain_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec_ref(v_xs_2640_);
lean_dec(v___x_2638_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object* v_es_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
size_t v_sz_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v_sz_2654_ = lean_array_size(v_es_2648_);
v___x_2655_ = ((size_t)0ULL);
lean_inc_ref(v_es_2648_);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2654_, v___x_2655_, v_es_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_a_2657_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; lean_object* v___f_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; lean_object* v___x_2664_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = lean_unsigned_to_nat(1u);
v___f_2661_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2661_, 0, v___x_2660_);
lean_closure_set(v___f_2661_, 1, v_es_2648_);
v___x_2662_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2663_ = 0;
v___x_2664_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_2659_, v___x_2662_, v___f_2661_, v___x_2663_, v___x_2663_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_2664_;
}
else
{
lean_dec_ref(v_es_2648_);
return v___x_2658_;
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec_ref(v_es_2648_);
v_a_2665_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2656_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2656_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object* v_es_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object* v_a_2680_, lean_object* v_domain_2681_, lean_object* v___x_2682_, lean_object* v_type_2683_, uint8_t v___x_2684_, lean_object* v_x_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = l_List_lengthTR___redArg(v_a_2680_);
lean_inc_ref(v_x_2685_);
v___x_2692_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2691_, v_domain_2681_, v___x_2682_, v_x_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___x_2691_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = lean_unsigned_to_nat(1u);
v___x_2695_ = lean_mk_empty_array_with_capacity(v___x_2694_);
lean_inc_ref(v___x_2695_);
v___x_2696_ = lean_array_push(v___x_2695_, v_a_2693_);
v___x_2697_ = l_Lean_Meta_instantiateForall(v_type_2683_, v___x_2696_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec_ref(v___x_2696_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = lean_array_push(v___x_2695_, v_x_2685_);
v___x_2700_ = 0;
v___x_2701_ = 1;
v___x_2702_ = l_Lean_Meta_mkForallFVars(v___x_2699_, v_a_2698_, v___x_2700_, v___x_2684_, v___x_2684_, v___x_2701_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec_ref(v___x_2699_);
return v___x_2702_;
}
else
{
lean_dec_ref(v___x_2695_);
lean_dec_ref(v_x_2685_);
return v___x_2697_;
}
}
else
{
lean_dec_ref(v_x_2685_);
lean_dec_ref(v_type_2683_);
return v___x_2692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object* v_a_2703_, lean_object* v_domain_2704_, lean_object* v___x_2705_, lean_object* v_type_2706_, lean_object* v___x_2707_, lean_object* v_x_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
uint8_t v___x_788__boxed_2714_; lean_object* v_res_2715_; 
v___x_788__boxed_2714_ = lean_unbox(v___x_2707_);
v_res_2715_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2703_, v_domain_2704_, v___x_2705_, v_type_2706_, v___x_788__boxed_2714_, v_x_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___x_2705_);
lean_dec(v_a_2703_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object* v_a_2716_, lean_object* v_domain_2717_, lean_object* v_type_2718_, size_t v_sz_2719_, size_t v_i_2720_, lean_object* v_bs_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v___x_2727_; 
v___x_2727_ = lean_usize_dec_lt(v_i_2720_, v_sz_2719_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; 
lean_dec_ref(v_type_2718_);
lean_dec_ref(v_domain_2717_);
lean_dec(v_a_2716_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v_bs_2721_);
return v___x_2728_;
}
else
{
lean_object* v_v_2729_; lean_object* v___x_2730_; lean_object* v_bs_x27_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___f_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_v_2729_ = lean_array_uget(v_bs_2721_, v_i_2720_);
v___x_2730_ = lean_unsigned_to_nat(0u);
v_bs_x27_2731_ = lean_array_uset(v_bs_2721_, v_i_2720_, v___x_2730_);
v___x_2732_ = lean_usize_to_nat(v_i_2720_);
v___x_2733_ = lean_box(v___x_2727_);
lean_inc_ref(v_type_2718_);
lean_inc_ref(v_domain_2717_);
lean_inc(v_a_2716_);
v___f_2734_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2734_, 0, v_a_2716_);
lean_closure_set(v___f_2734_, 1, v_domain_2717_);
lean_closure_set(v___f_2734_, 2, v___x_2732_);
lean_closure_set(v___f_2734_, 3, v_type_2718_);
lean_closure_set(v___f_2734_, 4, v___x_2733_);
v___x_2735_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2736_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_2735_, v_v_2729_, v___f_2734_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; size_t v___x_2738_; size_t v___x_2739_; lean_object* v___x_2740_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = ((size_t)1ULL);
v___x_2739_ = lean_usize_add(v_i_2720_, v___x_2738_);
v___x_2740_ = lean_array_uset(v_bs_x27_2731_, v_i_2720_, v_a_2737_);
v_i_2720_ = v___x_2739_;
v_bs_2721_ = v___x_2740_;
goto _start;
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec_ref(v_bs_x27_2731_);
lean_dec_ref(v_type_2718_);
lean_dec_ref(v_domain_2717_);
lean_dec(v_a_2716_);
v_a_2742_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2736_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2736_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object* v_a_2750_, lean_object* v_domain_2751_, lean_object* v_type_2752_, lean_object* v_sz_2753_, lean_object* v_i_2754_, lean_object* v_bs_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
size_t v_sz_boxed_2761_; size_t v_i_boxed_2762_; lean_object* v_res_2763_; 
v_sz_boxed_2761_ = lean_unbox_usize(v_sz_2753_);
lean_dec(v_sz_2753_);
v_i_boxed_2762_ = lean_unbox_usize(v_i_2754_);
lean_dec(v_i_2754_);
v_res_2763_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2750_, v_domain_2751_, v_type_2752_, v_sz_boxed_2761_, v_i_boxed_2762_, v_bs_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object* v_n_2764_, lean_object* v_type_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; uint8_t v___x_2791_; 
v___x_2791_ = l_Lean_Expr_isForall(v_type_2765_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v___x_2792_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_2793_ = l_Lean_MessageData_ofExpr(v_type_2765_);
v___x_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2794_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
v___y_2772_ = v_a_2766_;
v___y_2773_ = v_a_2767_;
v___y_2774_ = v_a_2768_;
v___y_2775_ = v_a_2769_;
goto v___jp_2771_;
}
v___jp_2771_:
{
lean_object* v_domain_2776_; lean_object* v___x_2777_; 
v_domain_2776_ = l_Lean_Expr_bindingDomain_x21(v_type_2765_);
lean_inc_ref(v_domain_2776_);
v___x_2777_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_2764_, v_domain_2776_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; size_t v_sz_2780_; size_t v___x_2781_; lean_object* v___x_2782_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_n(v_a_2778_, 2);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = lean_array_mk(v_a_2778_);
v_sz_2780_ = lean_array_size(v___x_2779_);
v___x_2781_ = ((size_t)0ULL);
v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2778_, v_domain_2776_, v_type_2765_, v_sz_2780_, v___x_2781_, v___x_2779_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
return v___x_2782_;
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref(v_domain_2776_);
lean_dec_ref(v_type_2765_);
v_a_2783_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2777_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2777_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object* v_n_2804_, lean_object* v_type_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2804_, v_type_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_n_2804_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object* v_a_2812_, lean_object* v_domain_2813_, lean_object* v_type_2814_, lean_object* v_as_2815_, size_t v_sz_2816_, size_t v_i_2817_, lean_object* v_bs_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2812_, v_domain_2813_, v_type_2814_, v_sz_2816_, v_i_2817_, v_bs_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object* v_a_2825_, lean_object* v_domain_2826_, lean_object* v_type_2827_, lean_object* v_as_2828_, lean_object* v_sz_2829_, lean_object* v_i_2830_, lean_object* v_bs_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
size_t v_sz_boxed_2837_; size_t v_i_boxed_2838_; lean_object* v_res_2839_; 
v_sz_boxed_2837_ = lean_unbox_usize(v_sz_2829_);
lean_dec(v_sz_2829_);
v_i_boxed_2838_ = lean_unbox_usize(v_i_2830_);
lean_dec(v_i_2830_);
v_res_2839_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2825_, v_domain_2826_, v_type_2827_, v_as_2828_, v_sz_boxed_2837_, v_i_boxed_2838_, v_bs_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec_ref(v_as_2828_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object* v_argsPacker_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_array_get_size(v_argsPacker_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object* v_argsPacker_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_2842_);
lean_dec_ref(v_argsPacker_2842_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t v_sz_2844_, size_t v_i_2845_, lean_object* v_bs_2846_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_usize_dec_lt(v_i_2845_, v_sz_2844_);
if (v___x_2847_ == 0)
{
return v_bs_2846_;
}
else
{
lean_object* v_v_2848_; lean_object* v___x_2849_; lean_object* v_bs_x27_2850_; lean_object* v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v_v_2848_ = lean_array_uget(v_bs_2846_, v_i_2845_);
v___x_2849_ = lean_unsigned_to_nat(0u);
v_bs_x27_2850_ = lean_array_uset(v_bs_2846_, v_i_2845_, v___x_2849_);
v___x_2851_ = lean_array_get_size(v_v_2848_);
lean_dec(v_v_2848_);
v___x_2852_ = ((size_t)1ULL);
v___x_2853_ = lean_usize_add(v_i_2845_, v___x_2852_);
v___x_2854_ = lean_array_uset(v_bs_x27_2850_, v_i_2845_, v___x_2851_);
v_i_2845_ = v___x_2853_;
v_bs_2846_ = v___x_2854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object* v_sz_2856_, lean_object* v_i_2857_, lean_object* v_bs_2858_){
_start:
{
size_t v_sz_boxed_2859_; size_t v_i_boxed_2860_; lean_object* v_res_2861_; 
v_sz_boxed_2859_ = lean_unbox_usize(v_sz_2856_);
lean_dec(v_sz_2856_);
v_i_boxed_2860_ = lean_unbox_usize(v_i_2857_);
lean_dec(v_i_2857_);
v_res_2861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_2859_, v_i_boxed_2860_, v_bs_2858_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object* v_argsPacker_2862_){
_start:
{
size_t v_sz_2863_; size_t v___x_2864_; lean_object* v___x_2865_; 
v_sz_2863_ = lean_array_size(v_argsPacker_2862_);
v___x_2864_ = ((size_t)0ULL);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2863_, v___x_2864_, v_argsPacker_2862_);
return v___x_2865_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0(void){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Array_instInhabited(lean_box(0));
return v___x_2866_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object* v_argsPacker_2867_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = lean_array_get_size(v_argsPacker_2867_);
v___x_2869_ = lean_unsigned_to_nat(1u);
v___x_2870_ = lean_nat_dec_eq(v___x_2868_, v___x_2869_);
if (v___x_2870_ == 0)
{
return v___x_2870_;
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2871_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2872_ = lean_unsigned_to_nat(0u);
v___x_2873_ = lean_array_get_borrowed(v___x_2871_, v_argsPacker_2867_, v___x_2872_);
v___x_2874_ = lean_array_get_size(v___x_2873_);
v___x_2875_ = lean_nat_dec_eq(v___x_2874_, v___x_2869_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object* v_argsPacker_2876_){
_start:
{
uint8_t v_res_2877_; lean_object* v_r_2878_; 
v_res_2877_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2876_);
lean_dec_ref(v_argsPacker_2876_);
v_r_2878_ = lean_box(v_res_2877_);
return v_r_2878_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__2(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2881_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__1));
v___x_2882_ = lean_unsigned_to_nat(2u);
v___x_2883_ = lean_unsigned_to_nat(472u);
v___x_2884_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2885_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2886_ = l_mkPanicMessageWithDecl(v___x_2885_, v___x_2884_, v___x_2883_, v___x_2882_, v___x_2881_);
return v___x_2886_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__4(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2888_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__3));
v___x_2889_ = lean_unsigned_to_nat(2u);
v___x_2890_ = lean_unsigned_to_nat(473u);
v___x_2891_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2892_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2893_ = l_mkPanicMessageWithDecl(v___x_2892_, v___x_2891_, v___x_2890_, v___x_2889_, v___x_2888_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object* v_argsPacker_2894_, lean_object* v_domain_2895_, lean_object* v_fidx_2896_, lean_object* v_args_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = lean_array_get_size(v_argsPacker_2894_);
v___x_2904_ = lean_nat_dec_lt(v_fidx_2896_, v___x_2903_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_dec(v_fidx_2896_);
lean_dec_ref(v_domain_2895_);
v___x_2905_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__2, &l_Lean_Meta_ArgsPacker_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__2);
v___x_2906_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2905_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
return v___x_2906_;
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2907_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2908_ = lean_array_get_size(v_args_2897_);
v___x_2909_ = lean_array_get_borrowed(v___x_2907_, v_argsPacker_2894_, v_fidx_2896_);
v___x_2910_ = lean_array_get_size(v___x_2909_);
v___x_2911_ = lean_nat_dec_eq(v___x_2908_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec(v_fidx_2896_);
lean_dec_ref(v_domain_2895_);
v___x_2912_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__4, &l_Lean_Meta_ArgsPacker_pack___closed__4_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__4);
v___x_2913_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2912_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; 
lean_inc_ref(v_domain_2895_);
v___x_2914_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_2903_, v_domain_2895_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = l_Lean_instInhabitedExpr;
lean_inc(v_fidx_2896_);
v___x_2917_ = l_List_get_x21Internal___redArg(v___x_2916_, v_a_2915_, v_fidx_2896_);
lean_dec(v_a_2915_);
v___x_2918_ = l_Lean_Meta_ArgsPacker_Unary_pack(v___x_2917_, v_args_2897_);
lean_dec(v___x_2917_);
v___x_2919_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2903_, v_domain_2895_, v_fidx_2896_, v___x_2918_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
lean_dec(v_fidx_2896_);
return v___x_2919_;
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_fidx_2896_);
lean_dec_ref(v_domain_2895_);
v_a_2920_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2914_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2914_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object* v_argsPacker_2928_, lean_object* v_domain_2929_, lean_object* v_fidx_2930_, lean_object* v_args_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2928_, v_domain_2929_, v_fidx_2930_, v_args_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec_ref(v_args_2931_);
lean_dec_ref(v_argsPacker_2928_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object* v_argsPacker_2938_, lean_object* v_e_2939_){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_argsPacker_2938_);
v___x_2941_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_2940_, v_e_2939_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_box(0);
return v___x_2942_;
}
else
{
lean_object* v_val_2943_; lean_object* v_fst_2944_; lean_object* v_snd_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2965_; 
v_val_2943_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_val_2943_);
lean_dec_ref_known(v___x_2941_, 1);
v_fst_2944_ = lean_ctor_get(v_val_2943_, 0);
v_snd_2945_ = lean_ctor_get(v_val_2943_, 1);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_val_2943_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2947_ = v_val_2943_;
v_isShared_2948_ = v_isSharedCheck_2965_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_snd_2945_);
lean_inc(v_fst_2944_);
lean_dec(v_val_2943_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2965_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2949_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2950_ = lean_array_get_borrowed(v___x_2949_, v_argsPacker_2938_, v_fst_2944_);
v___x_2951_ = lean_array_get_size(v___x_2950_);
v___x_2952_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_2951_, v_snd_2945_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2953_; 
lean_del_object(v___x_2947_);
lean_dec(v_fst_2944_);
v___x_2953_ = lean_box(0);
return v___x_2953_;
}
else
{
lean_object* v_val_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2964_; 
v_val_2954_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2956_ = v___x_2952_;
v_isShared_2957_ = v_isSharedCheck_2964_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_val_2954_);
lean_dec(v___x_2952_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2964_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v_val_2954_);
v___x_2959_ = v___x_2947_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_fst_2944_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_val_2954_);
v___x_2959_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2961_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___x_2959_);
v___x_2961_ = v___x_2956_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object* v_argsPacker_2966_, lean_object* v_e_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_2966_, v_e_2967_);
lean_dec_ref(v_argsPacker_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object* v_as_2969_, lean_object* v_bs_2970_, lean_object* v_i_2971_, lean_object* v_cs_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = lean_array_get_size(v_as_2969_);
v___x_2979_ = lean_nat_dec_lt(v_i_2971_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_i_2971_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_cs_2972_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; uint8_t v___x_2982_; 
v___x_2981_ = lean_array_get_size(v_bs_2970_);
v___x_2982_ = lean_nat_dec_lt(v_i_2971_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
lean_dec(v_i_2971_);
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_cs_2972_);
return v___x_2983_;
}
else
{
lean_object* v_a_2984_; lean_object* v_b_2985_; lean_object* v___x_2986_; 
v_a_2984_ = lean_array_fget_borrowed(v_as_2969_, v_i_2971_);
v_b_2985_ = lean_array_fget_borrowed(v_bs_2970_, v_i_2971_);
lean_inc(v_b_2985_);
lean_inc(v_a_2984_);
v___x_2986_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_a_2984_, v_b_2985_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2988_ = lean_unsigned_to_nat(1u);
v___x_2989_ = lean_nat_add(v_i_2971_, v___x_2988_);
lean_dec(v_i_2971_);
v___x_2990_ = lean_array_push(v_cs_2972_, v_a_2987_);
v_i_2971_ = v___x_2989_;
v_cs_2972_ = v___x_2990_;
goto _start;
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v_cs_2972_);
lean_dec(v_i_2971_);
v_a_2992_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2986_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2986_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object* v_as_3000_, lean_object* v_bs_3001_, lean_object* v_i_3002_, lean_object* v_cs_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_3000_, v_bs_3001_, v_i_3002_, v_cs_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec_ref(v_bs_3001_);
lean_dec_ref(v_as_3000_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object* v_argsPacker_3010_, lean_object* v_types_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = lean_unsigned_to_nat(0u);
v___x_3018_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_3019_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_argsPacker_3010_, v_types_3011_, v___x_3017_, v___x_3018_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_3020_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
return v___x_3021_;
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
v_a_3022_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3019_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3019_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object* v_argsPacker_3030_, lean_object* v_types_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_3030_, v_types_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
lean_dec(v_a_3033_);
lean_dec_ref(v_a_3032_);
lean_dec_ref(v_types_3031_);
lean_dec_ref(v_argsPacker_3030_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object* v_as_3038_, lean_object* v_bs_3039_, lean_object* v_i_3040_, lean_object* v_cs_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3047_ = lean_array_get_size(v_as_3038_);
v___x_3048_ = lean_nat_dec_lt(v_i_3040_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec(v_i_3040_);
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v_cs_3041_);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = lean_array_get_size(v_bs_3039_);
v___x_3051_ = lean_nat_dec_lt(v_i_3040_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
lean_dec(v_i_3040_);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_cs_3041_);
return v___x_3052_;
}
else
{
lean_object* v_a_3053_; lean_object* v_b_3054_; lean_object* v___x_3055_; 
v_a_3053_ = lean_array_fget_borrowed(v_as_3038_, v_i_3040_);
v_b_3054_ = lean_array_fget_borrowed(v_bs_3039_, v_i_3040_);
lean_inc(v_b_3054_);
lean_inc(v_a_3053_);
v___x_3055_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_a_3053_, v_b_3054_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
v___x_3057_ = lean_unsigned_to_nat(1u);
v___x_3058_ = lean_nat_add(v_i_3040_, v___x_3057_);
lean_dec(v_i_3040_);
v___x_3059_ = lean_array_push(v_cs_3041_, v_a_3056_);
v_i_3040_ = v___x_3058_;
v_cs_3041_ = v___x_3059_;
goto _start;
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v_cs_3041_);
lean_dec(v_i_3040_);
v_a_3061_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3055_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3055_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object* v_as_3069_, lean_object* v_bs_3070_, lean_object* v_i_3071_, lean_object* v_cs_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3069_, v_bs_3070_, v_i_3071_, v_cs_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec_ref(v_bs_3070_);
lean_dec_ref(v_as_3069_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object* v_argsPacker_3079_, lean_object* v_es_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_unsigned_to_nat(0u);
v___x_3087_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_3088_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3079_, v_es_3080_, v___x_3086_, v___x_3087_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3090_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3090_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_a_3089_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
return v___x_3090_;
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
v_a_3091_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3088_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3088_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object* v_argsPacker_3099_, lean_object* v_es_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3099_, v_es_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
lean_dec_ref(v_es_3100_);
lean_dec_ref(v_argsPacker_3099_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object* v_argsPacker_3107_, lean_object* v_resultType_3108_, lean_object* v_es_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_3117_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3107_, v_es_3109_, v___x_3115_, v___x_3116_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_3108_, v_a_3118_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
return v___x_3119_;
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_resultType_3108_);
v_a_3120_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3117_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3117_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object* v_argsPacker_3128_, lean_object* v_resultType_3129_, lean_object* v_es_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3128_, v_resultType_3129_, v_es_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec_ref(v_es_3130_);
lean_dec_ref(v_argsPacker_3128_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object* v_argsPacker_3137_, lean_object* v_es_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = lean_unsigned_to_nat(0u);
v___x_3145_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_3146_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3137_, v_es_3138_, v___x_3144_, v___x_3145_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3146_, 1);
v___x_3148_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_a_3147_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
return v___x_3148_;
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_a_3149_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3146_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3146_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object* v_argsPacker_3157_, lean_object* v_es_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3157_, v_es_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec_ref(v_es_3158_);
lean_dec_ref(v_argsPacker_3157_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object* v_msg_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___f_3171_; lean_object* v___x_920__overap_3172_; lean_object* v___x_3173_; 
v___f_3171_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_920__overap_3172_ = lean_panic_fn_borrowed(v___f_3171_, v_msg_3165_);
lean_inc(v___y_3169_);
lean_inc_ref(v___y_3168_);
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
v___x_3173_ = lean_apply_5(v___x_920__overap_3172_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, lean_box(0));
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object* v_msg_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object* v_a_3181_, lean_object* v___x_3182_, lean_object* v_i_3183_, lean_object* v_e_3184_, lean_object* v_x_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = l_List_lengthTR___redArg(v_a_3181_);
lean_inc_ref(v_x_3185_);
v___x_3192_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_3191_, v___x_3182_, v_i_3183_, v_x_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___x_3191_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; uint8_t v___x_3200_; uint8_t v___x_3201_; lean_object* v___x_3202_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
v___x_3194_ = lean_unsigned_to_nat(1u);
v___x_3195_ = lean_mk_empty_array_with_capacity(v___x_3194_);
lean_inc_ref(v___x_3195_);
v___x_3196_ = lean_array_push(v___x_3195_, v_x_3185_);
v___x_3197_ = lean_array_push(v___x_3195_, v_a_3193_);
v___x_3198_ = l_Lean_Expr_beta(v_e_3184_, v___x_3197_);
v___x_3199_ = 0;
v___x_3200_ = 1;
v___x_3201_ = 1;
v___x_3202_ = l_Lean_Meta_mkLambdaFVars(v___x_3196_, v___x_3198_, v___x_3199_, v___x_3200_, v___x_3199_, v___x_3200_, v___x_3201_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec_ref(v___x_3196_);
return v___x_3202_;
}
else
{
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_e_3184_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object* v_a_3203_, lean_object* v___x_3204_, lean_object* v_i_3205_, lean_object* v_e_3206_, lean_object* v_x_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3203_, v___x_3204_, v_i_3205_, v_e_3206_, v_x_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v_i_3205_);
lean_dec(v_a_3203_);
return v_res_3213_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__0));
v___x_3216_ = l_Lean_stringToMessageData(v___x_3215_);
return v___x_3216_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3219_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__3));
v___x_3220_ = lean_unsigned_to_nat(4u);
v___x_3221_ = lean_unsigned_to_nat(538u);
v___x_3222_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__2));
v___x_3223_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_3224_ = l_mkPanicMessageWithDecl(v___x_3223_, v___x_3222_, v___x_3221_, v___x_3220_, v___x_3219_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object* v_argsPacker_3225_, lean_object* v_e_3226_, lean_object* v_i_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v___x_3233_; 
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v_a_3228_);
lean_inc_ref(v_e_3226_);
v___x_3233_ = lean_infer_type(v_e_3226_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3235_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3233_, 1);
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v_a_3228_);
v___x_3235_ = lean_whnf(v_a_3234_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v_n_3252_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; uint8_t v___x_3282_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = l_Lean_instInhabitedExpr;
v___x_3238_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v_n_3252_ = lean_array_get_size(v_argsPacker_3225_);
v___x_3282_ = l_Lean_Expr_isForall(v_a_3236_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__4, &l_Lean_Meta_ArgsPacker_curryProj___closed__4_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4);
v___x_3284_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v___x_3283_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_dec_ref_known(v___x_3284_, 1);
v___y_3254_ = v_a_3228_;
v___y_3255_ = v_a_3229_;
v___y_3256_ = v_a_3230_;
v___y_3257_ = v_a_3231_;
goto v___jp_3253_;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_a_3236_);
lean_dec(v_i_3227_);
lean_dec_ref(v_e_3226_);
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
v___y_3254_ = v_a_3228_;
v___y_3255_ = v_a_3229_;
v___y_3256_ = v_a_3230_;
v___y_3257_ = v_a_3231_;
goto v___jp_3253_;
}
v___jp_3239_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_inc(v_i_3227_);
v___x_3246_ = l_List_get_x21Internal___redArg(v___x_3237_, v___y_3241_, v_i_3227_);
lean_dec(v___y_3241_);
v___x_3247_ = l_Lean_Expr_bindingName_x21(v_a_3236_);
lean_dec(v_a_3236_);
v___x_3248_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3247_, v___x_3246_, v___y_3240_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = lean_array_get_borrowed(v___x_3238_, v_argsPacker_3225_, v_i_3227_);
lean_dec(v_i_3227_);
lean_inc(v___x_3250_);
v___x_3251_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v___x_3250_, v_a_3249_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
return v___x_3251_;
}
else
{
lean_dec(v_i_3227_);
return v___x_3248_;
}
}
v___jp_3253_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = l_Lean_Expr_bindingDomain_x21(v_a_3236_);
lean_inc_ref(v___x_3258_);
v___x_3259_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_3252_, v___x_3258_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___f_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc_n(v_a_3260_, 2);
lean_dec_ref_known(v___x_3259_, 1);
lean_inc(v_i_3227_);
v___f_3261_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3261_, 0, v_a_3260_);
lean_closure_set(v___f_3261_, 1, v___x_3258_);
lean_closure_set(v___f_3261_, 2, v_i_3227_);
lean_closure_set(v___f_3261_, 3, v_e_3226_);
v___x_3262_ = l_List_lengthTR___redArg(v_a_3260_);
v___x_3263_ = lean_nat_dec_lt(v_i_3227_, v___x_3262_);
lean_dec(v___x_3262_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref(v___f_3261_);
lean_dec(v_a_3260_);
lean_dec(v_a_3236_);
lean_dec(v_i_3227_);
v___x_3264_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__1, &l_Lean_Meta_ArgsPacker_curryProj___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1);
v___x_3265_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3264_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
else
{
v___y_3240_ = v___f_3261_;
v___y_3241_ = v_a_3260_;
v___y_3242_ = v___y_3254_;
v___y_3243_ = v___y_3255_;
v___y_3244_ = v___y_3256_;
v___y_3245_ = v___y_3257_;
goto v___jp_3239_;
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref(v___x_3258_);
lean_dec(v_a_3236_);
lean_dec(v_i_3227_);
lean_dec_ref(v_e_3226_);
v_a_3274_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3259_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3259_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
else
{
lean_dec(v_i_3227_);
lean_dec_ref(v_e_3226_);
return v___x_3235_;
}
}
else
{
lean_dec(v_i_3227_);
lean_dec_ref(v_e_3226_);
return v___x_3233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object* v_argsPacker_3293_, lean_object* v_e_3294_, lean_object* v_i_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3293_, v_e_3294_, v_i_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec_ref(v_argsPacker_3293_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object* v_as_3302_, lean_object* v_bs_3303_, lean_object* v_i_3304_, lean_object* v_cs_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = lean_array_get_size(v_as_3302_);
v___x_3312_ = lean_nat_dec_lt(v_i_3304_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec(v_i_3304_);
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v_cs_3305_);
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = lean_array_get_size(v_bs_3303_);
v___x_3315_ = lean_nat_dec_lt(v_i_3304_, v___x_3314_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; 
lean_dec(v_i_3304_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v_cs_3305_);
return v___x_3316_;
}
else
{
lean_object* v_a_3317_; lean_object* v_b_3318_; lean_object* v___x_3319_; 
v_a_3317_ = lean_array_fget_borrowed(v_as_3302_, v_i_3304_);
v_b_3318_ = lean_array_fget_borrowed(v_bs_3303_, v_i_3304_);
lean_inc(v_b_3318_);
lean_inc(v_a_3317_);
v___x_3319_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_3317_, v_b_3318_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v___x_3321_ = lean_unsigned_to_nat(1u);
v___x_3322_ = lean_nat_add(v_i_3304_, v___x_3321_);
lean_dec(v_i_3304_);
v___x_3323_ = lean_array_push(v_cs_3305_, v_a_3320_);
v_i_3304_ = v___x_3322_;
v_cs_3305_ = v___x_3323_;
goto _start;
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec_ref(v_cs_3305_);
lean_dec(v_i_3304_);
v_a_3325_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3319_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3319_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object* v_as_3333_, lean_object* v_bs_3334_, lean_object* v_i_3335_, lean_object* v_cs_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3333_, v_bs_3334_, v_i_3335_, v_cs_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec_ref(v_bs_3334_);
lean_dec_ref(v_as_3333_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object* v_argsPacker_3343_, lean_object* v_t_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = lean_array_get_size(v_argsPacker_3343_);
v___x_3351_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v___x_3350_, v_t_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3351_, 1);
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_3355_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_argsPacker_3343_, v_a_3352_, v___x_3353_, v___x_3354_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3352_);
return v___x_3355_;
}
else
{
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object* v_argsPacker_3356_, lean_object* v_t_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3356_, v_t_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec_ref(v_argsPacker_3356_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object* v_upperBound_3364_, lean_object* v_argsPacker_3365_, lean_object* v_e_3366_, lean_object* v_a_3367_, lean_object* v_b_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v___x_3374_; 
v___x_3374_ = lean_nat_dec_lt(v_a_3367_, v_upperBound_3364_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; 
lean_dec(v_a_3367_);
lean_dec_ref(v_e_3366_);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_b_3368_);
return v___x_3375_;
}
else
{
lean_object* v___x_3376_; 
lean_inc(v_a_3367_);
lean_inc_ref(v_e_3366_);
v___x_3376_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3365_, v_e_3366_, v_a_3367_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = lean_array_push(v_b_3368_, v_a_3377_);
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = lean_nat_add(v_a_3367_, v___x_3379_);
lean_dec(v_a_3367_);
v_a_3367_ = v___x_3380_;
v_b_3368_ = v___x_3378_;
goto _start;
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec_ref(v_b_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_e_3366_);
v_a_3382_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3376_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3376_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object* v_upperBound_3390_, lean_object* v_argsPacker_3391_, lean_object* v_e_3392_, lean_object* v_a_3393_, lean_object* v_b_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3390_, v_argsPacker_3391_, v_e_3392_, v_a_3393_, v_b_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v_argsPacker_3391_);
lean_dec(v_upperBound_3390_);
return v_res_3400_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curry___closed__0(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_unsigned_to_nat(0u);
v___x_3402_ = l_Lean_Level_ofNat(v___x_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object* v_argsPacker_3403_, lean_object* v_e_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v_es_3412_; lean_object* v___x_3413_; 
v___x_3410_ = lean_array_get_size(v_argsPacker_3403_);
v___x_3411_ = lean_unsigned_to_nat(0u);
v_es_3412_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_3413_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_3410_, v_argsPacker_3403_, v_e_3404_, v___x_3411_, v_es_3412_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v___x_3415_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curry___closed__0, &l_Lean_Meta_ArgsPacker_curry___closed__0_once, _init_l_Lean_Meta_ArgsPacker_curry___closed__0);
v___x_3416_ = l_Lean_Meta_PProdN_mk(v___x_3415_, v_a_3414_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
return v___x_3416_;
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_a_3417_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3413_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3413_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object* v_argsPacker_3425_, lean_object* v_e_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3425_, v_e_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
lean_dec(v_a_3430_);
lean_dec_ref(v_a_3429_);
lean_dec(v_a_3428_);
lean_dec_ref(v_a_3427_);
lean_dec_ref(v_argsPacker_3425_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object* v_upperBound_3433_, lean_object* v_argsPacker_3434_, lean_object* v_e_3435_, lean_object* v_inst_3436_, lean_object* v_R_3437_, lean_object* v_a_3438_, lean_object* v_b_3439_, lean_object* v_c_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3433_, v_argsPacker_3434_, v_e_3435_, v_a_3438_, v_b_3439_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object* v_upperBound_3447_, lean_object* v_argsPacker_3448_, lean_object* v_e_3449_, lean_object* v_inst_3450_, lean_object* v_R_3451_, lean_object* v_a_3452_, lean_object* v_b_3453_, lean_object* v_c_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3447_, v_argsPacker_3448_, v_e_3449_, v_inst_3450_, v_R_3451_, v_a_3452_, v_b_3453_, v_c_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec_ref(v_argsPacker_3448_);
lean_dec(v_upperBound_3447_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object* v_a_3461_, lean_object* v_argsPacker_3462_, lean_object* v_name_3463_, lean_object* v_k_3464_, lean_object* v_tail_3465_, lean_object* v_x_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3461_, v_argsPacker_3462_, v_name_3463_, v_k_3464_, v_tail_3465_, v_x_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object* v_argsPacker_3473_, lean_object* v_name_3474_, lean_object* v_k_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
if (lean_obj_tag(v_a_3476_) == 0)
{
lean_object* v___x_3483_; 
lean_dec(v_name_3474_);
lean_dec_ref(v_argsPacker_3473_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc(v_a_3479_);
lean_inc_ref(v_a_3478_);
v___x_3483_ = lean_apply_6(v_k_3475_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, lean_box(0));
return v___x_3483_;
}
else
{
lean_object* v_head_3484_; lean_object* v_tail_3485_; lean_object* v___f_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v_head_3484_ = lean_ctor_get(v_a_3476_, 0);
lean_inc(v_head_3484_);
v_tail_3485_ = lean_ctor_get(v_a_3476_, 1);
lean_inc(v_tail_3485_);
lean_dec_ref_known(v_a_3476_, 2);
lean_inc(v_name_3474_);
lean_inc_ref(v_argsPacker_3473_);
lean_inc_ref(v_a_3477_);
v___f_3486_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3486_, 0, v_a_3477_);
lean_closure_set(v___f_3486_, 1, v_argsPacker_3473_);
lean_closure_set(v___f_3486_, 2, v_name_3474_);
lean_closure_set(v___f_3486_, 3, v_k_3475_);
lean_closure_set(v___f_3486_, 4, v_tail_3485_);
v___x_3487_ = lean_array_get_size(v_argsPacker_3473_);
lean_dec_ref(v_argsPacker_3473_);
v___x_3488_ = lean_unsigned_to_nat(1u);
v___x_3489_ = lean_nat_dec_eq(v___x_3487_, v___x_3488_);
if (v___x_3489_ == 0)
{
uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3490_ = 1;
v___x_3491_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3474_, v___x_3490_);
v___x_3492_ = lean_array_get_size(v_a_3477_);
lean_dec_ref(v_a_3477_);
v___x_3493_ = lean_nat_add(v___x_3492_, v___x_3488_);
v___x_3494_ = l_Nat_reprFast(v___x_3493_);
v___x_3495_ = lean_string_append(v___x_3491_, v___x_3494_);
lean_dec_ref(v___x_3494_);
v___x_3496_ = lean_box(0);
v___x_3497_ = l_Lean_Name_str___override(v___x_3496_, v___x_3495_);
v___x_3498_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3497_, v_head_3484_, v___f_3486_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
return v___x_3498_;
}
else
{
lean_object* v___x_3499_; 
lean_dec_ref(v_a_3477_);
v___x_3499_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_3474_, v_head_3484_, v___f_3486_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
return v___x_3499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object* v_a_3500_, lean_object* v_argsPacker_3501_, lean_object* v_name_3502_, lean_object* v_k_3503_, lean_object* v_tail_3504_, lean_object* v_x_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_array_push(v_a_3500_, v_x_3505_);
v___x_3512_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3501_, v_name_3502_, v_k_3503_, v_tail_3504_, v___x_3511_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object* v_argsPacker_3513_, lean_object* v_name_3514_, lean_object* v_k_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3513_, v_name_3514_, v_k_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object* v_00_u03b1_3524_, lean_object* v_argsPacker_3525_, lean_object* v_name_3526_, lean_object* v_k_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3525_, v_name_3526_, v_k_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object* v_00_u03b1_3536_, lean_object* v_argsPacker_3537_, lean_object* v_name_3538_, lean_object* v_k_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(v_00_u03b1_3536_, v_argsPacker_3537_, v_name_3538_, v_k_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
lean_dec(v_a_3545_);
lean_dec_ref(v_a_3544_);
lean_dec(v_a_3543_);
lean_dec_ref(v_a_3542_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object* v_argsPacker_3548_, lean_object* v_name_3549_, lean_object* v_type_3550_, lean_object* v_k_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3548_, v_type_3550_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = lean_array_to_list(v_a_3558_);
v___x_3560_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___closed__0));
v___x_3561_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3548_, v_name_3549_, v_k_3551_, v___x_3559_, v___x_3560_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
return v___x_3561_;
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec_ref(v_k_3551_);
lean_dec(v_name_3549_);
lean_dec_ref(v_argsPacker_3548_);
v_a_3562_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3557_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3557_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object* v_argsPacker_3570_, lean_object* v_name_3571_, lean_object* v_type_3572_, lean_object* v_k_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3570_, v_name_3571_, v_type_3572_, v_k_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object* v_00_u03b1_3580_, lean_object* v_argsPacker_3581_, lean_object* v_name_3582_, lean_object* v_type_3583_, lean_object* v_k_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3581_, v_name_3582_, v_type_3583_, v_k_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object* v_00_u03b1_3591_, lean_object* v_argsPacker_3592_, lean_object* v_name_3593_, lean_object* v_type_3594_, lean_object* v_k_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(v_00_u03b1_3591_, v_argsPacker_3592_, v_name_3593_, v_type_3594_, v_k_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object* v_argsPacker_3602_, lean_object* v_packedMotiveType_3603_, lean_object* v_type_3604_, lean_object* v_value_3605_, lean_object* v_k_3606_, lean_object* v_motives_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3602_, v_packedMotiveType_3603_, v_motives_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc_n(v_a_3614_, 2);
lean_dec_ref_known(v___x_3613_, 1);
v___x_3615_ = lean_unsigned_to_nat(1u);
v___x_3616_ = lean_mk_empty_array_with_capacity(v___x_3615_);
v___x_3617_ = lean_array_push(v___x_3616_, v_a_3614_);
v___x_3618_ = l_Lean_Meta_instantiateForall(v_type_3604_, v___x_3617_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec_ref(v___x_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3620_ = l_Lean_Expr_app___override(v_value_3605_, v_a_3614_);
lean_inc(v___y_3611_);
lean_inc_ref(v___y_3610_);
lean_inc(v___y_3609_);
lean_inc_ref(v___y_3608_);
v___x_3621_ = lean_apply_8(v_k_3606_, v_motives_3607_, v___x_3620_, v_a_3619_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, lean_box(0));
return v___x_3621_;
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec(v_a_3614_);
lean_dec_ref(v_motives_3607_);
lean_dec_ref(v_k_3606_);
lean_dec_ref(v_value_3605_);
v_a_3622_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3618_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3618_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec_ref(v_motives_3607_);
lean_dec_ref(v_k_3606_);
lean_dec_ref(v_value_3605_);
lean_dec_ref(v_type_3604_);
v_a_3630_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3613_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3613_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object* v_argsPacker_3638_, lean_object* v_packedMotiveType_3639_, lean_object* v_type_3640_, lean_object* v_value_3641_, lean_object* v_k_3642_, lean_object* v_motives_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3638_, v_packedMotiveType_3639_, v_type_3640_, v_value_3641_, v_k_3642_, v_motives_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec_ref(v_argsPacker_3638_);
return v_res_3649_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0));
v___x_3652_ = l_Lean_stringToMessageData(v___x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object* v_argsPacker_3656_, lean_object* v_value_3657_, lean_object* v_type_3658_, lean_object* v_k_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; uint8_t v___x_3694_; 
v___x_3694_ = l_Lean_Expr_isForall(v_type_3658_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec_ref(v_k_3659_);
lean_dec_ref(v_value_3657_);
lean_dec_ref(v_argsPacker_3656_);
v___x_3695_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3);
v___x_3696_ = l_Lean_MessageData_ofExpr(v_type_3658_);
v___x_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3697_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
else
{
v___y_3675_ = v_a_3660_;
v___y_3676_ = v_a_3661_;
v___y_3677_ = v_a_3662_;
v___y_3678_ = v_a_3663_;
goto v___jp_3674_;
}
v___jp_3665_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = l_Lean_Expr_bindingName_x21(v_type_3658_);
lean_dec_ref(v_type_3658_);
v___x_3673_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3656_, v___x_3672_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
return v___x_3673_;
}
v___jp_3674_:
{
lean_object* v_packedMotiveType_3679_; lean_object* v___f_3680_; uint8_t v___x_3681_; 
v_packedMotiveType_3679_ = l_Lean_Expr_bindingDomain_x21(v_type_3658_);
lean_inc_ref(v_type_3658_);
lean_inc_ref(v_packedMotiveType_3679_);
lean_inc_ref(v_argsPacker_3656_);
v___f_3680_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3680_, 0, v_argsPacker_3656_);
lean_closure_set(v___f_3680_, 1, v_packedMotiveType_3679_);
lean_closure_set(v___f_3680_, 2, v_type_3658_);
lean_closure_set(v___f_3680_, 3, v_value_3657_);
lean_closure_set(v___f_3680_, 4, v_k_3659_);
v___x_3681_ = l_Lean_Expr_isForall(v_packedMotiveType_3679_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec_ref(v___f_3680_);
lean_dec_ref(v_type_3658_);
lean_dec_ref(v_argsPacker_3656_);
v___x_3682_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1);
v___x_3683_ = l_Lean_indentExpr(v_packedMotiveType_3679_);
v___x_3684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3684_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3685_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3685_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
else
{
v___y_3666_ = v_packedMotiveType_3679_;
v___y_3667_ = v___f_3680_;
v___y_3668_ = v___y_3675_;
v___y_3669_ = v___y_3676_;
v___y_3670_ = v___y_3677_;
v___y_3671_ = v___y_3678_;
goto v___jp_3665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object* v_argsPacker_3707_, lean_object* v_value_3708_, lean_object* v_type_3709_, lean_object* v_k_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3707_, v_value_3708_, v_type_3709_, v_k_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object* v_00_u03b1_3717_, lean_object* v_argsPacker_3718_, lean_object* v_value_3719_, lean_object* v_type_3720_, lean_object* v_k_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3718_, v_value_3719_, v_type_3720_, v_k_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object* v_00_u03b1_3728_, lean_object* v_argsPacker_3729_, lean_object* v_value_3730_, lean_object* v_type_3731_, lean_object* v_k_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l_Lean_Meta_ArgsPacker_curryParam(v_00_u03b1_3728_, v_argsPacker_3729_, v_value_3730_, v_type_3731_, v_k_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
return v_res_3738_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ArgsPacker_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ArgsPacker_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_ArgsPacker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* initialize_Lean_Meta_ArgsPacker_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ArgsPacker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ArgsPacker_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_ArgsPacker(builtin);
}
#ifdef __cplusplus
}
#endif
