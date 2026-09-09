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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0_value)}};
static const lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(lean_object* v_arity_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_206_; 
v_fst_175_ = lean_ctor_get(v_a_174_, 0);
v_snd_176_ = lean_ctor_get(v_a_174_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_a_174_);
if (v_isSharedCheck_206_ == 0)
{
v___x_178_ = v_a_174_;
v_isShared_179_ = v_isSharedCheck_206_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snd_176_);
lean_inc(v_fst_175_);
lean_dec(v_a_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_206_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_180_ = lean_array_get_size(v_snd_176_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v___x_180_, v___x_181_);
v___x_183_ = lean_nat_dec_lt(v___x_182_, v_arity_173_);
lean_dec(v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_185_; 
if (v_isShared_179_ == 0)
{
v___x_185_ = v___x_178_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_fst_175_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_snd_176_);
v___x_185_ = v_reuseFailAlloc_187_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7));
v___x_189_ = lean_unsigned_to_nat(4u);
v___x_190_ = l_Lean_Expr_isAppOfArity(v_fst_175_, v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_del_object(v___x_178_);
lean_dec(v_snd_176_);
lean_dec(v_fst_175_);
v___x_191_ = lean_box(0);
return v___x_191_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_192_ = lean_unsigned_to_nat(2u);
v___x_193_ = l_Lean_Expr_getAppNumArgs(v_fst_175_);
v___x_194_ = lean_nat_sub(v___x_193_, v___x_192_);
v___x_195_ = lean_nat_sub(v___x_194_, v___x_181_);
lean_dec(v___x_194_);
v___x_196_ = l_Lean_Expr_getRevArg_x21(v_fst_175_, v___x_195_);
v___x_197_ = lean_array_push(v_snd_176_, v___x_196_);
v___x_198_ = lean_unsigned_to_nat(3u);
v___x_199_ = lean_nat_sub(v___x_193_, v___x_198_);
lean_dec(v___x_193_);
v___x_200_ = lean_nat_sub(v___x_199_, v___x_181_);
lean_dec(v___x_199_);
v___x_201_ = l_Lean_Expr_getRevArg_x21(v_fst_175_, v___x_200_);
lean_dec(v_fst_175_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_197_);
lean_ctor_set(v___x_178_, 0, v___x_201_);
v___x_203_ = v___x_178_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_197_);
v___x_203_ = v_reuseFailAlloc_205_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v_a_174_ = v___x_203_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg___boxed(lean_object* v_arity_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_207_, v_a_208_);
lean_dec(v_arity_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack(lean_object* v_arity_214_, lean_object* v_e_215_){
_start:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_nat_dec_eq(v_arity_214_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v_args_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_args_218_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_e_215_);
lean_ctor_set(v___x_219_, 1, v_args_218_);
v___x_220_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_214_, v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_232_; 
v_val_222_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_232_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_val_222_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v_fst_226_ = lean_ctor_get(v_val_222_, 0);
lean_inc(v_fst_226_);
v_snd_227_ = lean_ctor_get(v_val_222_, 1);
lean_inc(v_snd_227_);
lean_dec(v_val_222_);
v___x_228_ = lean_array_push(v_snd_227_, v_fst_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_228_);
v___x_230_ = v___x_224_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
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
else
{
lean_object* v___x_233_; 
lean_dec_ref(v_e_215_);
v___x_233_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1));
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___boxed(lean_object* v_arity_234_, lean_object* v_e_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v_arity_234_, v_e_235_);
lean_dec(v_arity_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(lean_object* v_arity_237_, lean_object* v_inst_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_237_, v_a_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___boxed(lean_object* v_arity_241_, lean_object* v_inst_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(v_arity_241_, v_inst_242_, v_a_243_);
lean_dec(v_arity_241_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(lean_object* v_upperBound_245_, lean_object* v_a_246_, lean_object* v_b_247_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = lean_nat_dec_lt(v_a_246_, v_upperBound_245_);
if (v___x_248_ == 0)
{
lean_dec(v_a_246_);
return v_b_247_;
}
else
{
lean_object* v_fst_249_; lean_object* v_snd_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_265_; 
v_fst_249_ = lean_ctor_get(v_b_247_, 0);
v_snd_250_ = lean_ctor_get(v_b_247_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_b_247_);
if (v_isSharedCheck_265_ == 0)
{
v___x_252_ = v_b_247_;
v_isShared_253_ = v_isSharedCheck_265_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_snd_250_);
lean_inc(v_fst_249_);
lean_dec(v_b_247_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_265_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
lean_inc(v_snd_250_);
v___x_257_ = l_Lean_mkProj(v___x_256_, v___x_254_, v_snd_250_);
v___x_258_ = lean_array_push(v_fst_249_, v___x_257_);
v___x_259_ = l_Lean_mkProj(v___x_256_, v___x_255_, v_snd_250_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___x_259_);
lean_ctor_set(v___x_252_, 0, v___x_258_);
v___x_261_ = v___x_252_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_264_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; 
v___x_262_ = lean_nat_add(v_a_246_, v___x_255_);
lean_dec(v_a_246_);
v_a_246_ = v___x_262_;
v_b_247_ = v___x_261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg___boxed(lean_object* v_upperBound_266_, lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_266_, v_a_267_, v_b_268_);
lean_dec(v_upperBound_266_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(lean_object* v_t_270_, lean_object* v_arity_271_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_nat_dec_eq(v_arity_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_result_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_281_; 
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_sub(v_arity_271_, v___x_274_);
v_result_276_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_result_276_);
lean_ctor_set(v___x_277_, 1, v_t_270_);
v___x_278_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v___x_275_, v___x_272_, v___x_277_);
lean_dec(v___x_275_);
v_fst_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_fst_279_);
v_snd_280_ = lean_ctor_get(v___x_278_, 1);
lean_inc(v_snd_280_);
lean_dec_ref(v___x_278_);
v___x_281_ = lean_array_push(v_fst_279_, v_snd_280_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; 
lean_dec_ref(v_t_270_);
v___x_282_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___boxed(lean_object* v_t_283_, lean_object* v_arity_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_t_283_, v_arity_284_);
lean_dec(v_arity_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(lean_object* v_upperBound_286_, lean_object* v_inst_287_, lean_object* v_R_288_, lean_object* v_a_289_, lean_object* v_b_290_, lean_object* v_c_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_286_, v_a_289_, v_b_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___boxed(lean_object* v_upperBound_293_, lean_object* v_inst_294_, lean_object* v_R_295_, lean_object* v_a_296_, lean_object* v_b_297_, lean_object* v_c_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(v_upperBound_293_, v_inst_294_, v_R_295_, v_a_296_, v_b_297_, v_c_298_);
lean_dec(v_upperBound_293_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___f_307_; lean_object* v___x_450__overap_308_; lean_object* v___x_309_; 
v___f_307_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_450__overap_308_ = lean_panic_fn_borrowed(v___f_307_, v_msg_301_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_309_ = lean_apply_5(v___x_450__overap_308_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, lean_box(0));
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___boxed(lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v_msg_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(lean_object* v_k_317_, lean_object* v_b_318_, lean_object* v_c_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; 
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
lean_inc(v___y_321_);
lean_inc_ref(v___y_320_);
v___x_325_ = lean_apply_7(v_k_317_, v_b_318_, v_c_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, lean_box(0));
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed(lean_object* v_k_326_, lean_object* v_b_327_, lean_object* v_c_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(v_k_326_, v_b_327_, v_c_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(lean_object* v_type_335_, lean_object* v_maxFVars_x3f_336_, lean_object* v_k_337_, uint8_t v_cleanupAnnotations_338_, uint8_t v_whnfType_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___f_345_; lean_object* v___x_346_; 
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_345_, 0, v_k_337_);
v___x_346_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_335_, v_maxFVars_x3f_336_, v___f_345_, v_cleanupAnnotations_338_, v_whnfType_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
v_a_355_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_346_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_346_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___boxed(lean_object* v_type_363_, lean_object* v_maxFVars_x3f_364_, lean_object* v_k_365_, lean_object* v_cleanupAnnotations_366_, lean_object* v_whnfType_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_373_; uint8_t v_whnfType_boxed_374_; lean_object* v_res_375_; 
v_cleanupAnnotations_boxed_373_ = lean_unbox(v_cleanupAnnotations_366_);
v_whnfType_boxed_374_ = lean_unbox(v_whnfType_367_);
v_res_375_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_363_, v_maxFVars_x3f_364_, v_k_365_, v_cleanupAnnotations_boxed_373_, v_whnfType_boxed_374_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(lean_object* v_00_u03b1_376_, lean_object* v_type_377_, lean_object* v_maxFVars_x3f_378_, lean_object* v_k_379_, uint8_t v_cleanupAnnotations_380_, uint8_t v_whnfType_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_377_, v_maxFVars_x3f_378_, v_k_379_, v_cleanupAnnotations_380_, v_whnfType_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___boxed(lean_object* v_00_u03b1_388_, lean_object* v_type_389_, lean_object* v_maxFVars_x3f_390_, lean_object* v_k_391_, lean_object* v_cleanupAnnotations_392_, lean_object* v_whnfType_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_399_; uint8_t v_whnfType_boxed_400_; lean_object* v_res_401_; 
v_cleanupAnnotations_boxed_399_ = lean_unbox(v_cleanupAnnotations_392_);
v_whnfType_boxed_400_ = lean_unbox(v_whnfType_393_);
v_res_401_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(v_00_u03b1_388_, v_type_389_, v_maxFVars_x3f_390_, v_k_391_, v_cleanupAnnotations_boxed_399_, v_whnfType_boxed_400_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(lean_object* v___x_402_, lean_object* v_type_403_, uint8_t v___x_404_, uint8_t v___x_405_, lean_object* v_tuple_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_inc_ref(v_tuple_406_);
v___x_412_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_tuple_406_, v___x_402_);
v___x_413_ = l_Lean_Meta_instantiateForall(v_type_403_, v___x_412_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec_ref(v___x_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_mk_empty_array_with_capacity(v___x_415_);
v___x_417_ = lean_array_push(v___x_416_, v_tuple_406_);
v___x_418_ = 1;
v___x_419_ = l_Lean_Meta_mkForallFVars(v___x_417_, v_a_414_, v___x_404_, v___x_405_, v___x_405_, v___x_418_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec_ref(v___x_417_);
return v___x_419_;
}
else
{
lean_dec_ref(v_tuple_406_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed(lean_object* v___x_420_, lean_object* v_type_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v_tuple_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
uint8_t v___x_1259__boxed_430_; uint8_t v___x_1260__boxed_431_; lean_object* v_res_432_; 
v___x_1259__boxed_430_ = lean_unbox(v___x_422_);
v___x_1260__boxed_431_ = lean_unbox(v___x_423_);
v_res_432_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(v___x_420_, v_type_421_, v___x_1259__boxed_430_, v___x_1260__boxed_431_, v_tuple_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___x_420_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(lean_object* v_k_433_, lean_object* v_b_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___x_440_; 
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
v___x_440_ = lean_apply_6(v_k_433_, v_b_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, lean_box(0));
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(v_k_441_, v_b_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(lean_object* v_name_449_, uint8_t v_bi_450_, lean_object* v_type_451_, lean_object* v_k_452_, uint8_t v_kind_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; 
v___f_459_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_459_, 0, v_k_452_);
v___x_460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_449_, v_bi_450_, v_type_451_, v___f_459_, v_kind_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_a_469_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_460_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_460_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___boxed(lean_object* v_name_477_, lean_object* v_bi_478_, lean_object* v_type_479_, lean_object* v_k_480_, lean_object* v_kind_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
uint8_t v_bi_boxed_487_; uint8_t v_kind_boxed_488_; lean_object* v_res_489_; 
v_bi_boxed_487_ = lean_unbox(v_bi_478_);
v_kind_boxed_488_ = lean_unbox(v_kind_481_);
v_res_489_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_477_, v_bi_boxed_487_, v_type_479_, v_k_480_, v_kind_boxed_488_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(lean_object* v_name_490_, lean_object* v_type_491_, lean_object* v_k_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
uint8_t v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = 0;
v___x_499_ = 0;
v___x_500_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_490_, v___x_498_, v_type_491_, v_k_492_, v___x_499_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg___boxed(lean_object* v_name_501_, lean_object* v_type_502_, lean_object* v_k_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_501_, v_type_502_, v_k_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_512_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1));
v___x_513_ = lean_unsigned_to_nat(6u);
v___x_514_ = lean_unsigned_to_nat(138u);
v___x_515_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0));
v___x_516_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_517_ = l_mkPanicMessageWithDecl(v___x_516_, v___x_515_, v___x_514_, v___x_513_, v___x_512_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(lean_object* v___x_521_, lean_object* v_type_522_, uint8_t v___x_523_, uint8_t v___x_524_, lean_object* v___x_525_, lean_object* v_varNames_526_, lean_object* v___x_527_, lean_object* v_xs_528_, lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_array_get_size(v_xs_528_);
v___x_536_ = lean_nat_dec_eq(v___x_535_, v___x_521_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec_ref(v_xs_528_);
lean_dec_ref(v_type_522_);
v___x_537_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2);
v___x_538_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_537_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Meta_ArgsPacker_Unary_packType(v_xs_528_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = lean_box(v___x_523_);
v___x_542_ = lean_box(v___x_524_);
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_543_, 0, v___x_535_);
lean_closure_set(v___f_543_, 1, v_type_522_);
lean_closure_set(v___f_543_, 2, v___x_541_);
lean_closure_set(v___f_543_, 3, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_dec_eq(v___x_535_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_547_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_546_, v_a_540_, v___f_543_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_array_get_borrowed(v___x_525_, v_varNames_526_, v___x_527_);
lean_inc(v___x_548_);
v___x_549_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_548_, v_a_540_, v___f_543_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_549_;
}
}
else
{
lean_dec_ref(v_type_522_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed(lean_object* v___x_550_, lean_object* v_type_551_, lean_object* v___x_552_, lean_object* v___x_553_, lean_object* v___x_554_, lean_object* v_varNames_555_, lean_object* v___x_556_, lean_object* v_xs_557_, lean_object* v_x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
uint8_t v___x_1412__boxed_564_; uint8_t v___x_1413__boxed_565_; lean_object* v_res_566_; 
v___x_1412__boxed_564_ = lean_unbox(v___x_552_);
v___x_1413__boxed_565_ = lean_unbox(v___x_553_);
v_res_566_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(v___x_550_, v_type_551_, v___x_1412__boxed_564_, v___x_1413__boxed_565_, v___x_554_, v_varNames_555_, v___x_556_, v_xs_557_, v_x_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v_x_558_);
lean_dec(v___x_556_);
lean_dec_ref(v_varNames_555_);
lean_dec(v___x_554_);
lean_dec(v___x_550_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType(lean_object* v_varNames_567_, lean_object* v_type_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_array_get_size(v_varNames_567_);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_nat_dec_eq(v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___f_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_577_ = lean_box(0);
v___x_578_ = 1;
v___x_579_ = lean_box(v___x_576_);
v___x_580_ = lean_box(v___x_578_);
lean_inc_ref(v_type_568_);
v___f_581_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed), 14, 7);
lean_closure_set(v___f_581_, 0, v___x_574_);
lean_closure_set(v___f_581_, 1, v_type_568_);
lean_closure_set(v___f_581_, 2, v___x_579_);
lean_closure_set(v___f_581_, 3, v___x_580_);
lean_closure_set(v___f_581_, 4, v___x_577_);
lean_closure_set(v___f_581_, 5, v_varNames_567_);
lean_closure_set(v___f_581_, 6, v___x_575_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_574_);
v___x_583_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_568_, v___x_582_, v___f_581_, v___x_576_, v___x_576_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref(v_varNames_567_);
v___x_584_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_585_ = l_Lean_mkArrow(v___x_584_, v_type_568_, v_a_571_, v_a_572_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___boxed(lean_object* v_varNames_586_, lean_object* v_type_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_586_, v_type_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(lean_object* v_00_u03b1_594_, lean_object* v_name_595_, uint8_t v_bi_596_, lean_object* v_type_597_, lean_object* v_k_598_, uint8_t v_kind_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_595_, v_bi_596_, v_type_597_, v_k_598_, v_kind_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_606_, lean_object* v_name_607_, lean_object* v_bi_608_, lean_object* v_type_609_, lean_object* v_k_610_, lean_object* v_kind_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v_bi_boxed_617_; uint8_t v_kind_boxed_618_; lean_object* v_res_619_; 
v_bi_boxed_617_ = lean_unbox(v_bi_608_);
v_kind_boxed_618_ = lean_unbox(v_kind_611_);
v_res_619_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(v_00_u03b1_606_, v_name_607_, v_bi_boxed_617_, v_type_609_, v_k_610_, v_kind_boxed_618_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(lean_object* v_00_u03b1_620_, lean_object* v_name_621_, lean_object* v_type_622_, lean_object* v_k_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_621_, v_type_622_, v_k_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___boxed(lean_object* v_00_u03b1_630_, lean_object* v_name_631_, lean_object* v_type_632_, lean_object* v_k_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(v_00_u03b1_630_, v_name_631_, v_type_632_, v_k_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(lean_object* v_msgData_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; lean_object* v_env_647_; lean_object* v___x_648_; lean_object* v_toCold_649_; lean_object* v_mctx_650_; lean_object* v_lctx_651_; lean_object* v_options_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_646_ = lean_st_ref_get(v___y_644_);
v_env_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc_ref(v_env_647_);
lean_dec(v___x_646_);
v___x_648_ = lean_st_ref_get(v___y_642_);
v_toCold_649_ = lean_ctor_get(v___y_643_, 0);
v_mctx_650_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_mctx_650_);
lean_dec(v___x_648_);
v_lctx_651_ = lean_ctor_get(v___y_641_, 2);
v_options_652_ = lean_ctor_get(v_toCold_649_, 2);
lean_inc_ref(v_options_652_);
lean_inc_ref(v_lctx_651_);
v___x_653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_653_, 0, v_env_647_);
lean_ctor_set(v___x_653_, 1, v_mctx_650_);
lean_ctor_set(v___x_653_, 2, v_lctx_651_);
lean_ctor_set(v___x_653_, 3, v_options_652_);
v___x_654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_msgData_640_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0___boxed(lean_object* v_msgData_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msgData_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(lean_object* v_msg_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_ref_669_; lean_object* v___x_670_; lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_ref_669_ = lean_ctor_get(v___y_666_, 2);
v___x_670_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msg_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
lean_inc(v_ref_669_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_ref_669_);
lean_ctor_set(v___x_675_, 1, v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 1);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg___boxed(lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed(lean_object** _args){
lean_object* v___x_690_ = _args[0];
lean_object* v___x_691_ = _args[1];
lean_object* v___x_692_ = _args[2];
lean_object* v_arg_693_ = _args[3];
lean_object* v_arg_694_ = _args[4];
lean_object* v_a_695_ = _args[5];
lean_object* v_alt_696_ = _args[6];
lean_object* v_tail_697_ = _args[7];
lean_object* v_u_698_ = _args[8];
lean_object* v___x_699_ = _args[9];
lean_object* v___x_700_ = _args[10];
lean_object* v___x_701_ = _args[11];
lean_object* v_head_702_ = _args[12];
lean_object* v_x_703_ = _args[13];
lean_object* v___y_704_ = _args[14];
lean_object* v___y_705_ = _args[15];
lean_object* v___y_706_ = _args[16];
lean_object* v___y_707_ = _args[17];
lean_object* v___y_708_ = _args[18];
_start:
{
uint8_t v___x_2926__boxed_709_; uint8_t v___x_2927__boxed_710_; uint8_t v___x_2928__boxed_711_; lean_object* v_res_712_; 
v___x_2926__boxed_709_ = lean_unbox(v___x_699_);
v___x_2927__boxed_710_ = lean_unbox(v___x_700_);
v___x_2928__boxed_711_ = lean_unbox(v___x_701_);
v_res_712_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(v___x_690_, v___x_691_, v___x_692_, v_arg_693_, v_arg_694_, v_a_695_, v_alt_696_, v_tail_697_, v_u_698_, v___x_2926__boxed_709_, v___x_2927__boxed_710_, v___x_2928__boxed_711_, v_head_702_, v_x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(lean_object* v_varNames_717_, lean_object* v_e_718_, lean_object* v_u_719_, lean_object* v_codomain_720_, lean_object* v_alt_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
if (lean_obj_tag(v_varNames_717_) == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v_codomain_720_);
lean_dec(v_u_719_);
lean_dec_ref(v_e_718_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v_alt_721_);
return v___x_727_;
}
else
{
lean_object* v_tail_728_; 
v_tail_728_ = lean_ctor_get(v_varNames_717_, 1);
lean_inc(v_tail_728_);
if (lean_obj_tag(v_tail_728_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref_known(v_varNames_717_, 2);
lean_dec_ref(v_codomain_720_);
lean_dec(v_u_719_);
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_mk_empty_array_with_capacity(v___x_729_);
v___x_731_ = lean_array_push(v___x_730_, v_e_718_);
v___x_732_ = l_Lean_Expr_beta(v_alt_721_, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v_head_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_790_; 
v_head_734_ = lean_ctor_get(v_varNames_717_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_varNames_717_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_varNames_717_, 1);
lean_dec(v_unused_791_);
v___x_736_ = v_varNames_717_;
v_isShared_737_ = v_isSharedCheck_790_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_head_734_);
lean_dec(v_varNames_717_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_790_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_head_738_; lean_object* v___x_739_; 
v_head_738_ = lean_ctor_get(v_tail_728_, 0);
lean_inc(v_head_738_);
lean_inc(v_a_725_);
lean_inc_ref(v_a_724_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc_ref(v_e_718_);
v___x_739_ = lean_infer_type(v_e_718_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_n(v_a_740_, 2);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_740_, v_a_723_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_752_ = l_Lean_Expr_cleanupAnnotations(v_a_742_);
v___x_753_ = l_Lean_Expr_isApp(v___x_752_);
if (v___x_753_ == 0)
{
lean_dec_ref(v___x_752_);
lean_dec(v_head_738_);
lean_del_object(v___x_736_);
lean_dec_ref_known(v_tail_728_, 2);
lean_dec(v_head_734_);
lean_dec_ref(v_alt_721_);
lean_dec_ref(v_codomain_720_);
lean_dec(v_u_719_);
lean_dec_ref(v_e_718_);
v___y_744_ = v_a_722_;
v___y_745_ = v_a_723_;
v___y_746_ = v_a_724_;
v___y_747_ = v_a_725_;
goto v___jp_743_;
}
else
{
lean_object* v_arg_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_arg_754_ = lean_ctor_get(v___x_752_, 1);
lean_inc_ref(v_arg_754_);
v___x_755_ = l_Lean_Expr_appFnCleanup___redArg(v___x_752_);
v___x_756_ = l_Lean_Expr_isApp(v___x_755_);
if (v___x_756_ == 0)
{
lean_dec_ref(v___x_755_);
lean_dec_ref(v_arg_754_);
lean_dec(v_head_738_);
lean_del_object(v___x_736_);
lean_dec_ref_known(v_tail_728_, 2);
lean_dec(v_head_734_);
lean_dec_ref(v_alt_721_);
lean_dec_ref(v_codomain_720_);
lean_dec(v_u_719_);
lean_dec_ref(v_e_718_);
v___y_744_ = v_a_722_;
v___y_745_ = v_a_723_;
v___y_746_ = v_a_724_;
v___y_747_ = v_a_725_;
goto v___jp_743_;
}
else
{
lean_object* v_arg_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_arg_757_ = lean_ctor_get(v___x_755_, 1);
lean_inc_ref(v_arg_757_);
v___x_758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_755_);
v___x_759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0));
v___x_760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_761_ = l_Lean_Expr_isConstOf(v___x_758_, v___x_760_);
lean_dec_ref(v___x_758_);
if (v___x_761_ == 0)
{
lean_dec_ref(v_arg_757_);
lean_dec_ref(v_arg_754_);
lean_dec(v_head_738_);
lean_del_object(v___x_736_);
lean_dec_ref_known(v_tail_728_, 2);
lean_dec(v_head_734_);
lean_dec_ref(v_alt_721_);
lean_dec_ref(v_codomain_720_);
lean_dec(v_u_719_);
lean_dec_ref(v_e_718_);
v___y_744_ = v_a_722_;
v___y_745_ = v_a_723_;
v___y_746_ = v_a_724_;
v___y_747_ = v_a_725_;
goto v___jp_743_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_mk_empty_array_with_capacity(v___x_762_);
lean_inc_ref(v_e_718_);
lean_inc_ref(v___x_763_);
v___x_764_ = lean_array_push(v___x_763_, v_e_718_);
v___x_765_ = 0;
v___x_766_ = 1;
v___x_767_ = l_Lean_Meta_mkLambdaFVars(v___x_764_, v_codomain_720_, v___x_765_, v___x_761_, v___x_765_, v___x_761_, v___x_766_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec_ref(v___x_764_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc_n(v_a_768_, 2);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = l_Lean_Expr_getAppFn(v_a_740_);
lean_dec(v_a_740_);
v___x_770_ = l_Lean_Expr_constLevels_x21(v___x_769_);
lean_dec_ref(v___x_769_);
v___x_771_ = lean_box(v___x_765_);
v___x_772_ = lean_box(v___x_761_);
v___x_773_ = lean_box(v___x_766_);
lean_inc(v_u_719_);
lean_inc_ref(v_arg_754_);
lean_inc_ref_n(v_arg_757_, 2);
lean_inc(v___x_770_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed), 19, 13);
lean_closure_set(v___f_774_, 0, v___x_763_);
lean_closure_set(v___f_774_, 1, v___x_759_);
lean_closure_set(v___f_774_, 2, v___x_770_);
lean_closure_set(v___f_774_, 3, v_arg_757_);
lean_closure_set(v___f_774_, 4, v_arg_754_);
lean_closure_set(v___f_774_, 5, v_a_768_);
lean_closure_set(v___f_774_, 6, v_alt_721_);
lean_closure_set(v___f_774_, 7, v_tail_728_);
lean_closure_set(v___f_774_, 8, v_u_719_);
lean_closure_set(v___f_774_, 9, v___x_771_);
lean_closure_set(v___f_774_, 10, v___x_772_);
lean_closure_set(v___f_774_, 11, v___x_773_);
lean_closure_set(v___f_774_, 12, v_head_738_);
v___x_775_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_734_, v_arg_757_, v___f_774_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_789_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_789_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_789_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_789_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3));
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v___x_770_);
lean_ctor_set(v___x_736_, 0, v_u_719_);
v___x_782_ = v___x_736_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_u_719_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_770_);
v___x_782_ = v_reuseFailAlloc_788_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_783_ = l_Lean_Expr_const___override(v___x_780_, v___x_782_);
v___x_784_ = l_Lean_mkApp5(v___x_783_, v_arg_757_, v_arg_754_, v_a_768_, v_e_718_, v_a_776_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_784_);
v___x_786_ = v___x_778_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_dec(v___x_770_);
lean_dec(v_a_768_);
lean_dec_ref(v_arg_757_);
lean_dec_ref(v_arg_754_);
lean_del_object(v___x_736_);
lean_dec(v_u_719_);
lean_dec_ref(v_e_718_);
return v___x_775_;
}
}
else
{
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_757_);
lean_dec_ref(v_arg_754_);
lean_dec(v_a_740_);
lean_dec(v_head_738_);
lean_del_object(v___x_736_);
lean_dec_ref_known(v_tail_728_, 2);
lean_dec(v_head_734_);
lean_dec_ref(v_alt_721_);
lean_dec(v_u_719_);
lean_dec_ref(v_e_718_);
return v___x_767_;
}
}
}
}
v___jp_743_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1);
v___x_749_ = l_Lean_MessageData_ofExpr(v_a_740_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_750_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
return v___x_751_;
}
}
else
{
lean_dec(v_a_740_);
lean_dec(v_head_738_);
lean_del_object(v___x_736_);
lean_dec(v_head_734_);
lean_dec_ref_known(v_tail_728_, 2);
lean_dec_ref(v_alt_721_);
lean_dec_ref(v_codomain_720_);
lean_dec(v_u_719_);
lean_dec_ref(v_e_718_);
return v___x_741_;
}
}
else
{
lean_dec(v_head_738_);
lean_del_object(v___x_736_);
lean_dec_ref_known(v_tail_728_, 2);
lean_dec(v_head_734_);
lean_dec_ref(v_alt_721_);
lean_dec_ref(v_codomain_720_);
lean_dec(v_u_719_);
lean_dec_ref(v_e_718_);
return v___x_739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(lean_object* v___x_792_, lean_object* v___x_793_, lean_object* v_arg_794_, lean_object* v_arg_795_, lean_object* v_x_796_, lean_object* v___x_797_, lean_object* v_a_798_, lean_object* v_alt_799_, lean_object* v___x_800_, lean_object* v_tail_801_, lean_object* v_u_802_, uint8_t v___x_803_, uint8_t v___x_804_, uint8_t v___x_805_, lean_object* v_y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_812_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6));
v___x_813_ = l_Lean_Name_mkStr2(v___x_792_, v___x_812_);
v___x_814_ = l_Lean_Expr_const___override(v___x_813_, v___x_793_);
lean_inc_ref_n(v_y_806_, 2);
lean_inc_ref(v_x_796_);
v___x_815_ = l_Lean_mkApp4(v___x_814_, v_arg_794_, v_arg_795_, v_x_796_, v_y_806_);
v___x_816_ = lean_array_push(v___x_797_, v___x_815_);
v___x_817_ = l_Lean_Expr_beta(v_a_798_, v___x_816_);
v___x_818_ = l_Lean_Expr_beta(v_alt_799_, v___x_800_);
v___x_819_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_tail_801_, v_y_806_, v_u_802_, v___x_817_, v___x_818_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = lean_unsigned_to_nat(2u);
v___x_822_ = lean_mk_empty_array_with_capacity(v___x_821_);
v___x_823_ = lean_array_push(v___x_822_, v_x_796_);
v___x_824_ = lean_array_push(v___x_823_, v_y_806_);
v___x_825_ = l_Lean_Meta_mkLambdaFVars(v___x_824_, v_a_820_, v___x_803_, v___x_804_, v___x_803_, v___x_804_, v___x_805_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref(v___x_824_);
return v___x_825_;
}
else
{
lean_dec_ref(v_y_806_);
lean_dec_ref(v_x_796_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_826_ = _args[0];
lean_object* v___x_827_ = _args[1];
lean_object* v_arg_828_ = _args[2];
lean_object* v_arg_829_ = _args[3];
lean_object* v_x_830_ = _args[4];
lean_object* v___x_831_ = _args[5];
lean_object* v_a_832_ = _args[6];
lean_object* v_alt_833_ = _args[7];
lean_object* v___x_834_ = _args[8];
lean_object* v_tail_835_ = _args[9];
lean_object* v_u_836_ = _args[10];
lean_object* v___x_837_ = _args[11];
lean_object* v___x_838_ = _args[12];
lean_object* v___x_839_ = _args[13];
lean_object* v_y_840_ = _args[14];
lean_object* v___y_841_ = _args[15];
lean_object* v___y_842_ = _args[16];
lean_object* v___y_843_ = _args[17];
lean_object* v___y_844_ = _args[18];
lean_object* v___y_845_ = _args[19];
_start:
{
uint8_t v___x_2947__boxed_846_; uint8_t v___x_2948__boxed_847_; uint8_t v___x_2949__boxed_848_; lean_object* v_res_849_; 
v___x_2947__boxed_846_ = lean_unbox(v___x_837_);
v___x_2948__boxed_847_ = lean_unbox(v___x_838_);
v___x_2949__boxed_848_ = lean_unbox(v___x_839_);
v_res_849_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(v___x_826_, v___x_827_, v_arg_828_, v_arg_829_, v_x_830_, v___x_831_, v_a_832_, v_alt_833_, v___x_834_, v_tail_835_, v_u_836_, v___x_2947__boxed_846_, v___x_2948__boxed_847_, v___x_2949__boxed_848_, v_y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v___x_852_, lean_object* v_arg_853_, lean_object* v_arg_854_, lean_object* v_a_855_, lean_object* v_alt_856_, lean_object* v_tail_857_, lean_object* v_u_858_, uint8_t v___x_859_, uint8_t v___x_860_, uint8_t v___x_861_, lean_object* v_head_862_, lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_inc_ref(v_x_863_);
lean_inc_ref(v___x_850_);
v___x_869_ = lean_array_push(v___x_850_, v_x_863_);
v___x_870_ = lean_box(v___x_859_);
v___x_871_ = lean_box(v___x_860_);
v___x_872_ = lean_box(v___x_861_);
lean_inc_ref(v___x_869_);
lean_inc_ref(v_arg_854_);
v___f_873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed), 20, 14);
lean_closure_set(v___f_873_, 0, v___x_851_);
lean_closure_set(v___f_873_, 1, v___x_852_);
lean_closure_set(v___f_873_, 2, v_arg_853_);
lean_closure_set(v___f_873_, 3, v_arg_854_);
lean_closure_set(v___f_873_, 4, v_x_863_);
lean_closure_set(v___f_873_, 5, v___x_850_);
lean_closure_set(v___f_873_, 6, v_a_855_);
lean_closure_set(v___f_873_, 7, v_alt_856_);
lean_closure_set(v___f_873_, 8, v___x_869_);
lean_closure_set(v___f_873_, 9, v_tail_857_);
lean_closure_set(v___f_873_, 10, v_u_858_);
lean_closure_set(v___f_873_, 11, v___x_870_);
lean_closure_set(v___f_873_, 12, v___x_871_);
lean_closure_set(v___f_873_, 13, v___x_872_);
v___x_874_ = l_Lean_Expr_beta(v_arg_854_, v___x_869_);
v___x_875_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_862_, v___x_874_, v___f_873_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___boxed(lean_object* v_varNames_876_, lean_object* v_e_877_, lean_object* v_u_878_, lean_object* v_codomain_879_, lean_object* v_alt_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_varNames_876_, v_e_877_, v_u_878_, v_codomain_879_, v_alt_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(lean_object* v_00_u03b1_887_, lean_object* v_msg_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___boxed(lean_object* v_00_u03b1_895_, lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(v_00_u03b1_895_, v_msg_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_905_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_906_ = lean_unsigned_to_nat(23u);
v___x_907_ = lean_unsigned_to_nat(180u);
v___x_908_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0));
v___x_909_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_910_ = l_mkPanicMessageWithDecl(v___x_909_, v___x_908_, v___x_907_, v___x_906_, v___x_905_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v_varNames_913_, lean_object* v_e_914_, uint8_t v___x_915_, uint8_t v___x_916_, lean_object* v_xs_917_, lean_object* v_codomain_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_array_get_size(v_xs_917_);
v___x_925_ = lean_nat_dec_eq(v___x_924_, v___x_911_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref(v_codomain_918_);
lean_dec_ref(v_e_914_);
lean_dec_ref(v_varNames_913_);
v___x_926_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2);
v___x_927_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_926_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; 
lean_inc_ref(v_codomain_918_);
v___x_928_ = l_Lean_Meta_getLevel(v_codomain_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = lean_array_fget_borrowed(v_xs_917_, v___x_912_);
v___x_931_ = lean_array_to_list(v_varNames_913_);
lean_inc(v___x_930_);
v___x_932_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v___x_931_, v___x_930_, v_a_929_, v_codomain_918_, v_e_914_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_911_);
lean_inc(v___x_930_);
v___x_935_ = lean_array_push(v___x_934_, v___x_930_);
v___x_936_ = 1;
v___x_937_ = l_Lean_Meta_mkLambdaFVars(v___x_935_, v_a_933_, v___x_915_, v___x_916_, v___x_915_, v___x_916_, v___x_936_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec_ref(v___x_935_);
return v___x_937_;
}
else
{
return v___x_932_;
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v_codomain_918_);
lean_dec_ref(v_e_914_);
lean_dec_ref(v_varNames_913_);
v_a_938_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_928_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_928_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed(lean_object* v___x_946_, lean_object* v___x_947_, lean_object* v_varNames_948_, lean_object* v_e_949_, lean_object* v___x_950_, lean_object* v___x_951_, lean_object* v_xs_952_, lean_object* v_codomain_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v___x_798__boxed_959_; uint8_t v___x_799__boxed_960_; lean_object* v_res_961_; 
v___x_798__boxed_959_ = lean_unbox(v___x_950_);
v___x_799__boxed_960_ = lean_unbox(v___x_951_);
v_res_961_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(v___x_946_, v___x_947_, v_varNames_948_, v_e_949_, v___x_798__boxed_959_, v___x_799__boxed_960_, v_xs_952_, v_codomain_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_xs_952_);
lean_dec(v___x_947_);
lean_dec(v___x_946_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry(lean_object* v_varNames_967_, lean_object* v_e_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_array_get_size(v_varNames_967_);
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_nat_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc_ref(v_e_968_);
v___x_977_ = lean_infer_type(v_e_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
lean_inc_ref(v_varNames_967_);
v___x_979_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_967_, v_a_978_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___f_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = 1;
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_box(v___x_976_);
v___x_984_ = lean_box(v___x_981_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed), 13, 6);
lean_closure_set(v___f_985_, 0, v___x_982_);
lean_closure_set(v___f_985_, 1, v___x_975_);
lean_closure_set(v___f_985_, 2, v_varNames_967_);
lean_closure_set(v___f_985_, 3, v_e_968_);
lean_closure_set(v___f_985_, 4, v___x_983_);
lean_closure_set(v___f_985_, 5, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_987_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_980_, v___x_986_, v___f_985_, v___x_976_, v___x_976_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_987_;
}
else
{
lean_dec_ref(v_e_968_);
lean_dec_ref(v_varNames_967_);
return v___x_979_;
}
}
else
{
lean_dec_ref(v_e_968_);
lean_dec_ref(v_varNames_967_);
return v___x_977_;
}
}
else
{
lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec_ref(v_varNames_967_);
v___x_988_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_989_ = 0;
v___x_990_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_991_ = l_Lean_mkLambda(v___x_988_, v___x_989_, v___x_990_, v_e_968_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___boxed(lean_object* v_varNames_993_, lean_object* v_e_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_varNames_993_, v_e_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_1000_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_dummy_1006_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1));
v_dummy_1006_ = l_Lean_Expr_const___override(v___x_1005_, v___x_1004_);
return v_dummy_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(lean_object* v_args_1007_, lean_object* v_type_1008_, lean_object* v_packedDomain_1009_, lean_object* v_tail_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_dummy_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_dummy_1017_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1011_);
v___x_1018_ = lean_array_push(v_args_1007_, v_x_1011_);
v___x_1019_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1008_, v_packedDomain_1009_, v_dummy_1017_, v___x_1018_, v_tail_1010_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; uint8_t v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = lean_mk_empty_array_with_capacity(v___x_1021_);
v___x_1023_ = lean_array_push(v___x_1022_, v_x_1011_);
v___x_1024_ = 0;
v___x_1025_ = 1;
v___x_1026_ = 1;
v___x_1027_ = l_Lean_Meta_mkForallFVars(v___x_1023_, v_a_1020_, v___x_1024_, v___x_1025_, v___x_1025_, v___x_1026_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec_ref(v___x_1023_);
return v___x_1027_;
}
else
{
lean_dec_ref(v_x_1011_);
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed(lean_object* v_args_1028_, lean_object* v_type_1029_, lean_object* v_packedDomain_1030_, lean_object* v_tail_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(v_args_1028_, v_type_1029_, v_packedDomain_1030_, v_tail_1031_, v_x_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed(lean_object* v_arg_1039_, lean_object* v_args_1040_, lean_object* v_type_1041_, lean_object* v_packedDomain_1042_, lean_object* v_tail_1043_, lean_object* v___x_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v___x_724__boxed_1051_; lean_object* v_res_1052_; 
v___x_724__boxed_1051_ = lean_unbox(v___x_1044_);
v_res_1052_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(v_arg_1039_, v_args_1040_, v_type_1041_, v_packedDomain_1042_, v_tail_1043_, v___x_724__boxed_1051_, v_x_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(lean_object* v_type_1053_, lean_object* v_packedDomain_1054_, lean_object* v_domain_1055_, lean_object* v_args_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; 
if (lean_obj_tag(v_a_1057_) == 0)
{
lean_object* v_packedArg_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v_domain_1055_);
v_packedArg_1072_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1054_, v_args_1056_);
lean_dec_ref(v_args_1056_);
lean_dec_ref(v_packedDomain_1054_);
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = lean_mk_empty_array_with_capacity(v___x_1073_);
v___x_1075_ = lean_array_push(v___x_1074_, v_packedArg_1072_);
v___x_1076_ = l_Lean_Meta_instantiateForall(v_type_1053_, v___x_1075_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec_ref(v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v_tail_1077_; 
v_tail_1077_ = lean_ctor_get(v_a_1057_, 1);
lean_inc(v_tail_1077_);
if (lean_obj_tag(v_tail_1077_) == 0)
{
lean_object* v_head_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; 
v_head_1078_ = lean_ctor_get(v_a_1057_, 0);
lean_inc(v_head_1078_);
lean_dec_ref_known(v_a_1057_, 2);
v___f_1079_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1079_, 0, v_args_1056_);
lean_closure_set(v___f_1079_, 1, v_type_1053_);
lean_closure_set(v___f_1079_, 2, v_packedDomain_1054_);
lean_closure_set(v___f_1079_, 3, v_tail_1077_);
v___x_1080_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1078_, v_domain_1055_, v___f_1079_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v___x_1080_;
}
else
{
lean_object* v_head_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_head_1081_ = lean_ctor_get(v_a_1057_, 0);
lean_inc(v_head_1081_);
lean_dec_ref_known(v_a_1057_, 2);
lean_inc_ref(v_domain_1055_);
v___x_1082_ = l_Lean_Expr_cleanupAnnotations(v_domain_1055_);
v___x_1083_ = l_Lean_Expr_isApp(v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v___x_1082_);
lean_dec(v_head_1081_);
lean_dec(v_tail_1077_);
lean_dec_ref(v_args_1056_);
lean_dec_ref(v_packedDomain_1054_);
lean_dec_ref(v_type_1053_);
v___y_1064_ = v_a_1058_;
v___y_1065_ = v_a_1059_;
v___y_1066_ = v_a_1060_;
v___y_1067_ = v_a_1061_;
goto v___jp_1063_;
}
else
{
lean_object* v_arg_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_arg_1084_ = lean_ctor_get(v___x_1082_, 1);
lean_inc_ref(v_arg_1084_);
v___x_1085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1082_);
v___x_1086_ = l_Lean_Expr_isApp(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v___x_1085_);
lean_dec_ref(v_arg_1084_);
lean_dec(v_head_1081_);
lean_dec(v_tail_1077_);
lean_dec_ref(v_args_1056_);
lean_dec_ref(v_packedDomain_1054_);
lean_dec_ref(v_type_1053_);
v___y_1064_ = v_a_1058_;
v___y_1065_ = v_a_1059_;
v___y_1066_ = v_a_1060_;
v___y_1067_ = v_a_1061_;
goto v___jp_1063_;
}
else
{
lean_object* v_arg_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_arg_1087_ = lean_ctor_get(v___x_1085_, 1);
lean_inc_ref(v_arg_1087_);
v___x_1088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1085_);
v___x_1089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1090_ = l_Lean_Expr_isConstOf(v___x_1088_, v___x_1089_);
lean_dec_ref(v___x_1088_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
lean_dec(v_head_1081_);
lean_dec(v_tail_1077_);
lean_dec_ref(v_args_1056_);
lean_dec_ref(v_packedDomain_1054_);
lean_dec_ref(v_type_1053_);
v___y_1064_ = v_a_1058_;
v___y_1065_ = v_a_1059_;
v___y_1066_ = v_a_1060_;
v___y_1067_ = v_a_1061_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; 
lean_dec_ref(v_domain_1055_);
v___x_1091_ = lean_box(v___x_1090_);
v___f_1092_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1092_, 0, v_arg_1084_);
lean_closure_set(v___f_1092_, 1, v_args_1056_);
lean_closure_set(v___f_1092_, 2, v_type_1053_);
lean_closure_set(v___f_1092_, 3, v_packedDomain_1054_);
lean_closure_set(v___f_1092_, 4, v_tail_1077_);
lean_closure_set(v___f_1092_, 5, v___x_1091_);
v___x_1093_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1081_, v_arg_1087_, v___f_1092_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v___x_1093_;
}
}
}
}
}
v___jp_1063_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1068_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1);
v___x_1069_ = l_Lean_MessageData_ofExpr(v_domain_1055_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1070_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(lean_object* v_arg_1094_, lean_object* v_args_1095_, lean_object* v_type_1096_, lean_object* v_packedDomain_1097_, lean_object* v_tail_1098_, uint8_t v___x_1099_, lean_object* v_x_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_mk_empty_array_with_capacity(v___x_1106_);
lean_inc_ref(v_x_1100_);
v___x_1108_ = lean_array_push(v___x_1107_, v_x_1100_);
lean_inc_ref(v___x_1108_);
v___x_1109_ = l_Lean_Expr_beta(v_arg_1094_, v___x_1108_);
v___x_1110_ = lean_array_push(v_args_1095_, v_x_1100_);
v___x_1111_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1096_, v_packedDomain_1097_, v___x_1109_, v___x_1110_, v_tail_1098_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; uint8_t v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v___x_1113_ = 0;
v___x_1114_ = 1;
v___x_1115_ = l_Lean_Meta_mkForallFVars(v___x_1108_, v_a_1112_, v___x_1113_, v___x_1099_, v___x_1099_, v___x_1114_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec_ref(v___x_1108_);
return v___x_1115_;
}
else
{
lean_dec_ref(v___x_1108_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___boxed(lean_object* v_type_1116_, lean_object* v_packedDomain_1117_, lean_object* v_domain_1118_, lean_object* v_args_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1116_, v_packedDomain_1117_, v_domain_1118_, v_args_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
return v_res_1126_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(lean_object* v_varNames_1130_, lean_object* v_type_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___x_1146_; 
v___x_1146_ = l_Lean_Expr_isForall(v_type_1131_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v_varNames_1130_);
v___x_1147_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_1148_ = l_Lean_MessageData_ofExpr(v_type_1131_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1149_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
v___y_1138_ = v_a_1132_;
v___y_1139_ = v_a_1133_;
v___y_1140_ = v_a_1134_;
v___y_1141_ = v_a_1135_;
goto v___jp_1137_;
}
v___jp_1137_:
{
lean_object* v_packedDomain_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_packedDomain_1142_ = l_Lean_Expr_bindingDomain_x21(v_type_1131_);
v___x_1143_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1144_ = lean_array_to_list(v_varNames_1130_);
lean_inc_ref(v_packedDomain_1142_);
v___x_1145_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1131_, v_packedDomain_1142_, v_packedDomain_1142_, v___x_1143_, v___x_1144_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___boxed(lean_object* v_varNames_1159_, lean_object* v_type_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_varNames_1159_, v_type_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
return v_res_1166_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0));
v___x_1169_ = l_Lean_stringToMessageData(v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(lean_object* v_args_1170_, lean_object* v_e_1171_, lean_object* v_packedDomain_1172_, lean_object* v_tail_1173_, lean_object* v_x_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_dummy_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_dummy_1180_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1174_);
v___x_1181_ = lean_array_push(v_args_1170_, v_x_1174_);
v___x_1182_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1171_, v_packedDomain_1172_, v_dummy_1180_, v___x_1181_, v_tail_1173_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_mk_empty_array_with_capacity(v___x_1184_);
v___x_1186_ = lean_array_push(v___x_1185_, v_x_1174_);
v___x_1187_ = 0;
v___x_1188_ = 1;
v___x_1189_ = 1;
v___x_1190_ = l_Lean_Meta_mkLambdaFVars(v___x_1186_, v_a_1183_, v___x_1187_, v___x_1188_, v___x_1187_, v___x_1188_, v___x_1189_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec_ref(v___x_1186_);
return v___x_1190_;
}
else
{
lean_dec_ref(v_x_1174_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed(lean_object* v_args_1191_, lean_object* v_e_1192_, lean_object* v_packedDomain_1193_, lean_object* v_tail_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(v_args_1191_, v_e_1192_, v_packedDomain_1193_, v_tail_1194_, v_x_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed(lean_object* v_arg_1202_, lean_object* v_args_1203_, lean_object* v_e_1204_, lean_object* v_packedDomain_1205_, lean_object* v_tail_1206_, lean_object* v___x_1207_, lean_object* v_x_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v___x_842__boxed_1214_; lean_object* v_res_1215_; 
v___x_842__boxed_1214_ = lean_unbox(v___x_1207_);
v_res_1215_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(v_arg_1202_, v_args_1203_, v_e_1204_, v_packedDomain_1205_, v_tail_1206_, v___x_842__boxed_1214_, v_x_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(lean_object* v_e_1216_, lean_object* v_packedDomain_1217_, lean_object* v_domain_1218_, lean_object* v_args_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; 
if (lean_obj_tag(v_a_1220_) == 0)
{
lean_object* v_packedArg_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec_ref(v_domain_1218_);
v_packedArg_1235_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1217_, v_args_1219_);
lean_dec_ref(v_args_1219_);
lean_dec_ref(v_packedDomain_1217_);
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_mk_empty_array_with_capacity(v___x_1236_);
v___x_1238_ = lean_array_push(v___x_1237_, v_packedArg_1235_);
v___x_1239_ = l_Lean_Expr_beta(v_e_1216_, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
else
{
lean_object* v_tail_1241_; 
v_tail_1241_ = lean_ctor_get(v_a_1220_, 1);
lean_inc(v_tail_1241_);
if (lean_obj_tag(v_tail_1241_) == 0)
{
lean_object* v_head_1242_; lean_object* v___f_1243_; lean_object* v___x_1244_; 
v_head_1242_ = lean_ctor_get(v_a_1220_, 0);
lean_inc(v_head_1242_);
lean_dec_ref_known(v_a_1220_, 2);
v___f_1243_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1243_, 0, v_args_1219_);
lean_closure_set(v___f_1243_, 1, v_e_1216_);
lean_closure_set(v___f_1243_, 2, v_packedDomain_1217_);
lean_closure_set(v___f_1243_, 3, v_tail_1241_);
v___x_1244_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1242_, v_domain_1218_, v___f_1243_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
return v___x_1244_;
}
else
{
lean_object* v_head_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_head_1245_ = lean_ctor_get(v_a_1220_, 0);
lean_inc(v_head_1245_);
lean_dec_ref_known(v_a_1220_, 2);
lean_inc_ref(v_domain_1218_);
v___x_1246_ = l_Lean_Expr_cleanupAnnotations(v_domain_1218_);
v___x_1247_ = l_Lean_Expr_isApp(v___x_1246_);
if (v___x_1247_ == 0)
{
lean_dec_ref(v___x_1246_);
lean_dec(v_head_1245_);
lean_dec(v_tail_1241_);
lean_dec_ref(v_args_1219_);
lean_dec_ref(v_packedDomain_1217_);
lean_dec_ref(v_e_1216_);
v___y_1227_ = v_a_1221_;
v___y_1228_ = v_a_1222_;
v___y_1229_ = v_a_1223_;
v___y_1230_ = v_a_1224_;
goto v___jp_1226_;
}
else
{
lean_object* v_arg_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_arg_1248_ = lean_ctor_get(v___x_1246_, 1);
lean_inc_ref(v_arg_1248_);
v___x_1249_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1246_);
v___x_1250_ = l_Lean_Expr_isApp(v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec_ref(v___x_1249_);
lean_dec_ref(v_arg_1248_);
lean_dec(v_head_1245_);
lean_dec(v_tail_1241_);
lean_dec_ref(v_args_1219_);
lean_dec_ref(v_packedDomain_1217_);
lean_dec_ref(v_e_1216_);
v___y_1227_ = v_a_1221_;
v___y_1228_ = v_a_1222_;
v___y_1229_ = v_a_1223_;
v___y_1230_ = v_a_1224_;
goto v___jp_1226_;
}
else
{
lean_object* v_arg_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_arg_1251_ = lean_ctor_get(v___x_1249_, 1);
lean_inc_ref(v_arg_1251_);
v___x_1252_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1249_);
v___x_1253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1254_ = l_Lean_Expr_isConstOf(v___x_1252_, v___x_1253_);
lean_dec_ref(v___x_1252_);
if (v___x_1254_ == 0)
{
lean_dec_ref(v_arg_1251_);
lean_dec_ref(v_arg_1248_);
lean_dec(v_head_1245_);
lean_dec(v_tail_1241_);
lean_dec_ref(v_args_1219_);
lean_dec_ref(v_packedDomain_1217_);
lean_dec_ref(v_e_1216_);
v___y_1227_ = v_a_1221_;
v___y_1228_ = v_a_1222_;
v___y_1229_ = v_a_1223_;
v___y_1230_ = v_a_1224_;
goto v___jp_1226_;
}
else
{
lean_object* v___x_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v_domain_1218_);
v___x_1255_ = lean_box(v___x_1254_);
v___f_1256_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1256_, 0, v_arg_1248_);
lean_closure_set(v___f_1256_, 1, v_args_1219_);
lean_closure_set(v___f_1256_, 2, v_e_1216_);
lean_closure_set(v___f_1256_, 3, v_packedDomain_1217_);
lean_closure_set(v___f_1256_, 4, v_tail_1241_);
lean_closure_set(v___f_1256_, 5, v___x_1255_);
v___x_1257_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1245_, v_arg_1251_, v___f_1256_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
return v___x_1257_;
}
}
}
}
}
v___jp_1226_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1);
v___x_1232_ = l_Lean_MessageData_ofExpr(v_domain_1218_);
v___x_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1233_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(lean_object* v_arg_1258_, lean_object* v_args_1259_, lean_object* v_e_1260_, lean_object* v_packedDomain_1261_, lean_object* v_tail_1262_, uint8_t v___x_1263_, lean_object* v_x_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_mk_empty_array_with_capacity(v___x_1270_);
lean_inc_ref(v_x_1264_);
v___x_1272_ = lean_array_push(v___x_1271_, v_x_1264_);
lean_inc_ref(v___x_1272_);
v___x_1273_ = l_Lean_Expr_beta(v_arg_1258_, v___x_1272_);
v___x_1274_ = lean_array_push(v_args_1259_, v_x_1264_);
v___x_1275_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1260_, v_packedDomain_1261_, v___x_1273_, v___x_1274_, v_tail_1262_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; uint8_t v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = 0;
v___x_1278_ = 1;
v___x_1279_ = l_Lean_Meta_mkLambdaFVars(v___x_1272_, v_a_1276_, v___x_1277_, v___x_1263_, v___x_1277_, v___x_1263_, v___x_1278_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec_ref(v___x_1272_);
return v___x_1279_;
}
else
{
lean_dec_ref(v___x_1272_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___boxed(lean_object* v_e_1280_, lean_object* v_packedDomain_1281_, lean_object* v_domain_1282_, lean_object* v_args_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1280_, v_packedDomain_1281_, v_domain_1282_, v_args_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
return v_res_1290_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1294_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_pack___closed__2, &l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2);
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_mk_empty_array_with_capacity(v___x_1295_);
v___x_1297_ = lean_array_push(v___x_1296_, v___x_1294_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(lean_object* v_varNames_1298_, lean_object* v_e_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = lean_array_get_size(v_varNames_1298_);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_nat_dec_eq(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_inc(v_a_1303_);
lean_inc_ref(v_a_1302_);
lean_inc(v_a_1301_);
lean_inc_ref(v_a_1300_);
lean_inc_ref(v_e_1299_);
v___x_1308_ = lean_infer_type(v_e_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1310_ = l_Lean_Meta_whnfForall(v_a_1309_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___x_1321_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1321_ = l_Lean_Expr_isForall(v_a_1311_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_e_1299_);
lean_dec_ref(v_varNames_1298_);
v___x_1322_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1);
v___x_1323_ = l_Lean_MessageData_ofExpr(v_a_1311_);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1324_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
v___y_1313_ = v_a_1300_;
v___y_1314_ = v_a_1301_;
v___y_1315_ = v_a_1302_;
v___y_1316_ = v_a_1303_;
goto v___jp_1312_;
}
v___jp_1312_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = l_Lean_Expr_bindingDomain_x21(v_a_1311_);
lean_dec(v_a_1311_);
v___x_1318_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1319_ = lean_array_to_list(v_varNames_1298_);
lean_inc_ref(v___x_1317_);
v___x_1320_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1299_, v___x_1317_, v___x_1317_, v___x_1318_, v___x_1319_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1320_;
}
}
else
{
lean_dec_ref(v_e_1299_);
lean_dec_ref(v_varNames_1298_);
return v___x_1310_;
}
}
else
{
lean_dec_ref(v_e_1299_);
lean_dec_ref(v_varNames_1298_);
return v___x_1308_;
}
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref(v_varNames_1298_);
v___x_1334_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2);
v___x_1335_ = l_Lean_Expr_beta(v_e_1299_, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___boxed(lean_object* v_varNames_1337_, lean_object* v_e_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v_varNames_1337_, v_e_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(lean_object* v_as_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1351_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_a_1359_ = lean_array_uget_borrowed(v_as_1348_, v_i_1350_);
v___x_1360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1361_ = lean_unsigned_to_nat(2u);
v___x_1362_ = lean_mk_empty_array_with_capacity(v___x_1361_);
lean_inc(v_a_1359_);
v___x_1363_ = lean_array_push(v___x_1362_, v_a_1359_);
v___x_1364_ = lean_array_push(v___x_1363_, v_b_1351_);
v___x_1365_ = l_Lean_Meta_mkAppM(v___x_1360_, v___x_1364_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; size_t v___x_1367_; size_t v___x_1368_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_add(v_i_1350_, v___x_1367_);
v_i_1350_ = v___x_1368_;
v_b_1351_ = v_a_1366_;
goto _start;
}
else
{
return v___x_1365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___boxed(lean_object* v_as_1370_, lean_object* v_sz_1371_, lean_object* v_i_1372_, lean_object* v_b_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
size_t v_sz_boxed_1379_; size_t v_i_boxed_1380_; lean_object* v_res_1381_; 
v_sz_boxed_1379_ = lean_unbox_usize(v_sz_1371_);
lean_dec(v_sz_1371_);
v_i_boxed_1380_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_res_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v_as_1370_, v_sz_boxed_1379_, v_i_boxed_1380_, v_b_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v_as_1370_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object* v_ds_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v_r_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; size_t v_sz_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1388_ = l_Lean_instInhabitedExpr;
v___x_1389_ = lean_array_get_size(v_ds_1382_);
v___x_1390_ = lean_unsigned_to_nat(1u);
v___x_1391_ = lean_nat_sub(v___x_1389_, v___x_1390_);
v_r_1392_ = lean_array_get(v___x_1388_, v_ds_1382_, v___x_1391_);
lean_dec(v___x_1391_);
v___x_1393_ = lean_array_pop(v_ds_1382_);
v___x_1394_ = l_Array_reverse___redArg(v___x_1393_);
v_sz_1395_ = lean_array_size(v___x_1394_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v___x_1394_, v_sz_1395_, v___x_1396_, v_r_1392_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec_ref(v___x_1394_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object* v_ds_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v_ds_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
return v_res_1404_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0));
v___x_1407_ = l_Lean_stringToMessageData(v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object* v_n_1408_, lean_object* v_type_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v_zero_1424_; uint8_t v_isZero_1425_; 
v_zero_1424_ = lean_unsigned_to_nat(0u);
v_isZero_1425_ = lean_nat_dec_eq(v_n_1408_, v_zero_1424_);
if (v_isZero_1425_ == 1)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v_type_1409_);
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
else
{
lean_object* v_one_1428_; lean_object* v_n_1429_; uint8_t v___x_1430_; 
v_one_1428_ = lean_unsigned_to_nat(1u);
v_n_1429_ = lean_nat_sub(v_n_1408_, v_one_1428_);
v___x_1430_ = lean_nat_dec_eq(v_n_1429_, v_zero_1424_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
lean_inc_ref(v_type_1409_);
v___x_1431_ = l_Lean_Expr_cleanupAnnotations(v_type_1409_);
v___x_1432_ = l_Lean_Expr_isApp(v___x_1431_);
if (v___x_1432_ == 0)
{
lean_dec_ref(v___x_1431_);
lean_dec(v_n_1429_);
v___y_1416_ = v_a_1410_;
v___y_1417_ = v_a_1411_;
v___y_1418_ = v_a_1412_;
v___y_1419_ = v_a_1413_;
goto v___jp_1415_;
}
else
{
lean_object* v_arg_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_arg_1433_ = lean_ctor_get(v___x_1431_, 1);
lean_inc_ref(v_arg_1433_);
v___x_1434_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1431_);
v___x_1435_ = l_Lean_Expr_isApp(v___x_1434_);
if (v___x_1435_ == 0)
{
lean_dec_ref(v___x_1434_);
lean_dec_ref(v_arg_1433_);
lean_dec(v_n_1429_);
v___y_1416_ = v_a_1410_;
v___y_1417_ = v_a_1411_;
v___y_1418_ = v_a_1412_;
v___y_1419_ = v_a_1413_;
goto v___jp_1415_;
}
else
{
lean_object* v_arg_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_arg_1436_ = lean_ctor_get(v___x_1434_, 1);
lean_inc_ref(v_arg_1436_);
v___x_1437_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1434_);
v___x_1438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1439_ = l_Lean_Expr_isConstOf(v___x_1437_, v___x_1438_);
lean_dec_ref(v___x_1437_);
if (v___x_1439_ == 0)
{
lean_dec_ref(v_arg_1436_);
lean_dec_ref(v_arg_1433_);
lean_dec(v_n_1429_);
v___y_1416_ = v_a_1410_;
v___y_1417_ = v_a_1411_;
v___y_1418_ = v_a_1412_;
v___y_1419_ = v_a_1413_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1440_; 
lean_dec_ref(v_type_1409_);
v___x_1440_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1429_, v_arg_1433_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
lean_dec(v_n_1429_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1449_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_arg_1436_);
lean_ctor_set(v___x_1445_, 1, v_a_1441_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1445_);
v___x_1447_ = v___x_1443_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_dec_ref(v_arg_1436_);
return v___x_1440_;
}
}
}
}
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v_n_1429_);
v___x_1450_ = lean_box(0);
v___x_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_type_1409_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
v___jp_1415_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1420_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1);
v___x_1421_ = l_Lean_MessageData_ofExpr(v_type_1409_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1422_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object* v_n_1453_, lean_object* v_type_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1453_, v_type_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_n_1453_);
return v_res_1460_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0(void){
_start:
{
lean_object* v___x_1461_; lean_object* v_dummy_1462_; 
v___x_1461_ = lean_box(0);
v_dummy_1462_ = l_Lean_Expr_sort___override(v___x_1461_);
return v_dummy_1462_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1465_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1));
v___x_1466_ = lean_unsigned_to_nat(8u);
v___x_1467_ = lean_unsigned_to_nat(276u);
v___x_1468_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0));
v___x_1469_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1470_ = l_mkPanicMessageWithDecl(v___x_1469_, v___x_1468_, v___x_1467_, v___x_1466_, v___x_1465_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(lean_object* v_i_1479_, lean_object* v_fidx_1480_, lean_object* v_numFuncs_1481_, lean_object* v_arg_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_x_1483_) == 5)
{
lean_object* v_fn_1492_; lean_object* v_arg_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_fn_1492_ = lean_ctor_get(v_x_1483_, 0);
lean_inc_ref(v_fn_1492_);
v_arg_1493_ = lean_ctor_get(v_x_1483_, 1);
lean_inc_ref(v_arg_1493_);
lean_dec_ref_known(v_x_1483_, 2);
v___x_1494_ = lean_array_set(v_x_1484_, v_x_1485_, v_arg_1493_);
v___x_1495_ = lean_nat_sub(v_x_1485_, v___x_1491_);
lean_dec(v_x_1485_);
v_x_1483_ = v_fn_1492_;
v_x_1484_ = v___x_1494_;
v_x_1485_ = v___x_1495_;
goto _start;
}
else
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
lean_dec(v_x_1485_);
v___x_1497_ = lean_array_get_size(v_x_1484_);
v___x_1498_ = lean_unsigned_to_nat(2u);
v___x_1499_ = lean_nat_dec_eq(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec_ref(v_x_1484_);
lean_dec_ref(v_x_1483_);
lean_dec_ref(v_arg_1482_);
v___x_1500_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2);
v___x_1501_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1500_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = l_Lean_instInhabitedExpr;
v___x_1503_ = lean_nat_dec_eq(v_i_1479_, v_fidx_1480_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = lean_nat_add(v_i_1479_, v___x_1491_);
v___x_1505_ = lean_array_get(v___x_1502_, v_x_1484_, v___x_1491_);
lean_inc(v___x_1505_);
v___x_1506_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1481_, v_fidx_1480_, v_arg_1482_, v___x_1504_, v___x_1505_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___x_1504_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1520_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1520_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1520_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1511_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1512_ = l_Lean_Expr_constLevels_x21(v_x_1483_);
lean_dec_ref(v_x_1483_);
v___x_1513_ = l_Lean_mkConst(v___x_1511_, v___x_1512_);
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = lean_array_get(v___x_1502_, v_x_1484_, v___x_1514_);
lean_dec_ref(v_x_1484_);
v___x_1516_ = l_Lean_mkApp3(v___x_1513_, v___x_1515_, v___x_1505_, v_a_1507_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1516_);
v___x_1518_ = v___x_1509_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
else
{
lean_dec(v___x_1505_);
lean_dec_ref(v_x_1484_);
lean_dec_ref(v_x_1483_);
return v___x_1506_;
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1521_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1522_ = l_Lean_Expr_constLevels_x21(v_x_1483_);
lean_dec_ref(v_x_1483_);
v___x_1523_ = l_Lean_mkConst(v___x_1521_, v___x_1522_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_array_get(v___x_1502_, v_x_1484_, v___x_1524_);
v___x_1526_ = lean_array_get(v___x_1502_, v_x_1484_, v___x_1491_);
lean_dec_ref(v_x_1484_);
v___x_1527_ = l_Lean_mkApp3(v___x_1523_, v___x_1525_, v___x_1526_, v_arg_1482_);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(lean_object* v_numFuncs_1529_, lean_object* v_fidx_1530_, lean_object* v_arg_1531_, lean_object* v_i_1532_, lean_object* v_type_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_nat_sub(v_numFuncs_1529_, v___x_1539_);
v___x_1541_ = lean_nat_dec_le(v___x_1540_, v_i_1532_);
lean_dec(v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Meta_whnfD(v_type_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v_dummy_1544_; lean_object* v_nargs_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_dummy_1544_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
v_nargs_1545_ = l_Lean_Expr_getAppNumArgs(v_a_1543_);
lean_inc(v_nargs_1545_);
v___x_1546_ = lean_mk_array(v_nargs_1545_, v_dummy_1544_);
v___x_1547_ = lean_nat_sub(v_nargs_1545_, v___x_1539_);
lean_dec(v_nargs_1545_);
v___x_1548_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1532_, v_fidx_1530_, v_numFuncs_1529_, v_arg_1531_, v_a_1543_, v___x_1546_, v___x_1547_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
return v___x_1548_;
}
else
{
lean_dec_ref(v_arg_1531_);
return v___x_1542_;
}
}
else
{
lean_object* v___x_1549_; 
lean_dec_ref(v_type_1533_);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_arg_1531_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___boxed(lean_object* v_numFuncs_1550_, lean_object* v_fidx_1551_, lean_object* v_arg_1552_, lean_object* v_i_1553_, lean_object* v_type_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1550_, v_fidx_1551_, v_arg_1552_, v_i_1553_, v_type_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_i_1553_);
lean_dec(v_fidx_1551_);
lean_dec(v_numFuncs_1550_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___boxed(lean_object* v_i_1561_, lean_object* v_fidx_1562_, lean_object* v_numFuncs_1563_, lean_object* v_arg_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1561_, v_fidx_1562_, v_numFuncs_1563_, v_arg_1564_, v_x_1565_, v_x_1566_, v_x_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v_numFuncs_1563_);
lean_dec(v_fidx_1562_);
lean_dec(v_i_1561_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object* v_numFuncs_1574_, lean_object* v_domain_1575_, lean_object* v_fidx_1576_, lean_object* v_arg_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1574_, v_fidx_1576_, v_arg_1577_, v___x_1583_, v_domain_1575_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object* v_numFuncs_1585_, lean_object* v_domain_1586_, lean_object* v_fidx_1587_, lean_object* v_arg_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v_numFuncs_1585_, v_domain_1586_, v_fidx_1587_, v_arg_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_fidx_1587_);
lean_dec(v_numFuncs_1585_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(lean_object* v_numFuncs_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_fst_1597_; lean_object* v_snd_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1633_; 
v_fst_1597_ = lean_ctor_get(v_a_1596_, 0);
v_snd_1598_ = lean_ctor_get(v_a_1596_, 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_a_1596_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1600_ = v_a_1596_;
v_isShared_1601_ = v_isSharedCheck_1633_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_snd_1598_);
lean_inc(v_fst_1597_);
lean_dec(v_a_1596_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1633_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_add(v_fst_1597_, v___x_1602_);
v___x_1604_ = lean_nat_dec_lt(v___x_1603_, v_numFuncs_1595_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1606_; 
lean_dec(v___x_1603_);
if (v_isShared_1601_ == 0)
{
v___x_1606_ = v___x_1600_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_fst_1597_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_snd_1598_);
v___x_1606_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
return v___x_1607_;
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1610_ = lean_unsigned_to_nat(3u);
v___x_1611_ = l_Lean_Expr_isAppOfArity(v_snd_1598_, v___x_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
lean_dec(v___x_1603_);
v___x_1612_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1613_ = l_Lean_Expr_isAppOfArity(v_snd_1598_, v___x_1612_, v___x_1610_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_del_object(v___x_1600_);
lean_dec(v_snd_1598_);
lean_dec(v_fst_1597_);
v___x_1614_ = lean_box(0);
return v___x_1614_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1615_ = lean_unsigned_to_nat(2u);
v___x_1616_ = l_Lean_Expr_getAppNumArgs(v_snd_1598_);
v___x_1617_ = lean_nat_sub(v___x_1616_, v___x_1615_);
lean_dec(v___x_1616_);
v___x_1618_ = lean_nat_sub(v___x_1617_, v___x_1602_);
lean_dec(v___x_1617_);
v___x_1619_ = l_Lean_Expr_getRevArg_x21(v_snd_1598_, v___x_1618_);
lean_dec(v_snd_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v___x_1619_);
v___x_1621_ = v___x_1600_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_fst_1597_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_dec(v_fst_1597_);
v___x_1624_ = lean_unsigned_to_nat(2u);
v___x_1625_ = l_Lean_Expr_getAppNumArgs(v_snd_1598_);
v___x_1626_ = lean_nat_sub(v___x_1625_, v___x_1624_);
lean_dec(v___x_1625_);
v___x_1627_ = lean_nat_sub(v___x_1626_, v___x_1602_);
lean_dec(v___x_1626_);
v___x_1628_ = l_Lean_Expr_getRevArg_x21(v_snd_1598_, v___x_1627_);
lean_dec(v_snd_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v___x_1628_);
lean_ctor_set(v___x_1600_, 0, v___x_1603_);
v___x_1630_ = v___x_1600_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
v_a_1596_ = v___x_1630_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg___boxed(lean_object* v_numFuncs_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1634_, v_a_1635_);
lean_dec(v_numFuncs_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object* v_numFuncs_1637_, lean_object* v_expr_1638_){
_start:
{
lean_object* v_funidx_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_funidx_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_funidx_1639_);
lean_ctor_set(v___x_1640_, 1, v_expr_1638_);
v___x_1641_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1637_, v___x_1640_);
if (lean_obj_tag(v___x_1641_) == 0)
{
return v___x_1641_;
}
else
{
lean_object* v_val_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1658_; 
v_val_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1658_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_val_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1658_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_fst_1646_; lean_object* v_snd_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1657_; 
v_fst_1646_ = lean_ctor_get(v_val_1642_, 0);
v_snd_1647_ = lean_ctor_get(v_val_1642_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_val_1642_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1649_ = v_val_1642_;
v_isShared_1650_ = v_isSharedCheck_1657_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_snd_1647_);
lean_inc(v_fst_1646_);
lean_dec(v_val_1642_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1657_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_fst_1646_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_snd_1647_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1654_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1652_);
v___x_1654_ = v___x_1644_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(lean_object* v_numFuncs_1659_, lean_object* v_expr_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v_numFuncs_1659_, v_expr_1660_);
lean_dec(v_numFuncs_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(lean_object* v_numFuncs_1662_, lean_object* v_inst_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1662_, v_a_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(lean_object* v_numFuncs_1666_, lean_object* v_inst_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(v_numFuncs_1666_, v_inst_1667_, v_a_1668_);
lean_dec(v_numFuncs_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object* v___x_1670_, lean_object* v___x_1671_, lean_object* v_types_1672_, lean_object* v_i_1673_, uint8_t v___x_1674_, uint8_t v___x_1675_, uint8_t v___x_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_inc_ref(v_x_1677_);
v___x_1683_ = lean_array_push(v___x_1670_, v_x_1677_);
v___x_1684_ = lean_array_get_borrowed(v___x_1671_, v_types_1672_, v_i_1673_);
v___x_1685_ = l_Lean_Expr_bindingBody_x21(v___x_1684_);
v___x_1686_ = lean_expr_instantiate1(v___x_1685_, v_x_1677_);
lean_dec_ref(v_x_1677_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = l_Lean_Meta_mkLambdaFVars(v___x_1683_, v___x_1686_, v___x_1674_, v___x_1675_, v___x_1674_, v___x_1675_, v___x_1676_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec_ref(v___x_1683_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object* v___x_1688_, lean_object* v___x_1689_, lean_object* v_types_1690_, lean_object* v_i_1691_, lean_object* v___x_1692_, lean_object* v___x_1693_, lean_object* v___x_1694_, lean_object* v_x_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
uint8_t v___x_1663__boxed_1701_; uint8_t v___x_1664__boxed_1702_; uint8_t v___x_1665__boxed_1703_; lean_object* v_res_1704_; 
v___x_1663__boxed_1701_ = lean_unbox(v___x_1692_);
v___x_1664__boxed_1702_ = lean_unbox(v___x_1693_);
v___x_1665__boxed_1703_ = lean_unbox(v___x_1694_);
v_res_1704_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v___x_1688_, v___x_1689_, v_types_1690_, v_i_1691_, v___x_1663__boxed_1701_, v___x_1664__boxed_1702_, v___x_1665__boxed_1703_, v_x_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v_i_1691_);
lean_dec_ref(v_types_1690_);
lean_dec_ref(v___x_1689_);
return v_res_1704_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1707_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1));
v___x_1708_ = lean_unsigned_to_nat(6u);
v___x_1709_ = lean_unsigned_to_nat(318u);
v___x_1710_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0));
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1712_ = l_mkPanicMessageWithDecl(v___x_1711_, v___x_1710_, v___x_1709_, v___x_1708_, v___x_1707_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object* v_i_1713_, lean_object* v___x_1714_, lean_object* v_types_1715_, lean_object* v_u_1716_, lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v___x_1720_, lean_object* v_x_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v___x_1723__boxed_1727_; uint8_t v___x_1724__boxed_1728_; uint8_t v___x_1725__boxed_1729_; lean_object* v_res_1730_; 
v___x_1723__boxed_1727_ = lean_unbox(v___x_1718_);
v___x_1724__boxed_1728_ = lean_unbox(v___x_1719_);
v___x_1725__boxed_1729_ = lean_unbox(v___x_1720_);
v_res_1730_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_i_1713_, v___x_1714_, v_types_1715_, v_u_1716_, v___x_1717_, v___x_1723__boxed_1727_, v___x_1724__boxed_1728_, v___x_1725__boxed_1729_, v_x_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___x_1714_);
lean_dec(v_i_1713_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object* v_types_1734_, lean_object* v_u_1735_, lean_object* v_x_1736_, lean_object* v_i_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1743_ = l_Lean_instInhabitedExpr;
v___x_1744_ = lean_array_get_size(v_types_1734_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_sub(v___x_1744_, v___x_1745_);
v___x_1747_ = lean_nat_dec_lt(v_i_1737_, v___x_1746_);
lean_dec(v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_u_1735_);
v___x_1748_ = lean_array_get(v___x_1743_, v_types_1734_, v_i_1737_);
lean_dec(v_i_1737_);
lean_dec_ref(v_types_1734_);
v___x_1749_ = l_Lean_Expr_bindingBody_x21(v___x_1748_);
lean_dec(v___x_1748_);
v___x_1750_ = lean_expr_instantiate1(v___x_1749_, v_x_1736_);
lean_dec_ref(v_x_1736_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; 
lean_inc(v_a_1741_);
lean_inc_ref(v_a_1740_);
lean_inc(v_a_1739_);
lean_inc_ref(v_a_1738_);
lean_inc_ref(v_x_1736_);
v___x_1752_ = lean_infer_type(v_x_1736_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l_Lean_Meta_whnfD(v_a_1753_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1757_ = lean_unsigned_to_nat(2u);
v___x_1758_ = l_Lean_Expr_isAppOfArity(v_a_1755_, v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_a_1755_);
lean_dec(v_i_1737_);
lean_dec_ref(v_x_1736_);
lean_dec(v_u_1735_);
lean_dec_ref(v_types_1734_);
v___x_1759_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
v___x_1760_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1759_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; 
lean_inc_n(v_u_1735_, 2);
v___x_1761_ = l_Lean_Level_succ___override(v_u_1735_);
v___x_1762_ = lean_mk_empty_array_with_capacity(v___x_1745_);
lean_inc_ref(v_x_1736_);
lean_inc_ref(v___x_1762_);
v___x_1763_ = lean_array_push(v___x_1762_, v_x_1736_);
v___x_1764_ = l_Lean_mkSort(v_u_1735_);
v___x_1765_ = 0;
v___x_1766_ = 1;
v___x_1767_ = l_Lean_Meta_mkLambdaFVars(v___x_1763_, v___x_1764_, v___x_1765_, v___x_1747_, v___x_1765_, v___x_1747_, v___x_1766_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
lean_dec_ref(v___x_1763_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1769_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_1770_ = l_Lean_Core_mkFreshUserName(v___x_1769_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_nargs_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___f_1776_; lean_object* v_dummy_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v_nargs_1772_ = l_Lean_Expr_getAppNumArgs(v_a_1755_);
v___x_1773_ = lean_box(v___x_1765_);
v___x_1774_ = lean_box(v___x_1747_);
v___x_1775_ = lean_box(v___x_1766_);
lean_inc(v_i_1737_);
lean_inc_ref(v_types_1734_);
lean_inc_ref(v___x_1762_);
v___f_1776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1776_, 0, v___x_1762_);
lean_closure_set(v___f_1776_, 1, v___x_1743_);
lean_closure_set(v___f_1776_, 2, v_types_1734_);
lean_closure_set(v___f_1776_, 3, v_i_1737_);
lean_closure_set(v___f_1776_, 4, v___x_1773_);
lean_closure_set(v___f_1776_, 5, v___x_1774_);
lean_closure_set(v___f_1776_, 6, v___x_1775_);
v_dummy_1777_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
lean_inc(v_nargs_1772_);
v___x_1778_ = lean_mk_array(v_nargs_1772_, v_dummy_1777_);
v___x_1779_ = lean_nat_sub(v_nargs_1772_, v___x_1745_);
lean_dec(v_nargs_1772_);
lean_inc(v_a_1755_);
v___x_1780_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1755_, v___x_1778_, v___x_1779_);
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = lean_array_get_borrowed(v___x_1743_, v___x_1780_, v___x_1781_);
lean_inc(v___x_1782_);
v___x_1783_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1771_, v___x_1782_, v___f_1776_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = l_Lean_Core_mkFreshUserName(v___x_1769_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___f_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1787_ = lean_box(v___x_1765_);
v___x_1788_ = lean_box(v___x_1747_);
v___x_1789_ = lean_box(v___x_1766_);
v___f_1790_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1790_, 0, v_i_1737_);
lean_closure_set(v___f_1790_, 1, v___x_1745_);
lean_closure_set(v___f_1790_, 2, v_types_1734_);
lean_closure_set(v___f_1790_, 3, v_u_1735_);
lean_closure_set(v___f_1790_, 4, v___x_1762_);
lean_closure_set(v___f_1790_, 5, v___x_1787_);
lean_closure_set(v___f_1790_, 6, v___x_1788_);
lean_closure_set(v___f_1790_, 7, v___x_1789_);
v___x_1791_ = lean_array_get(v___x_1743_, v___x_1780_, v___x_1745_);
v___x_1792_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1786_, v___x_1791_, v___f_1790_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1809_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1809_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1809_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1797_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
v___x_1798_ = l_Lean_Expr_getAppFn(v_a_1755_);
lean_dec(v_a_1755_);
v___x_1799_ = l_Lean_Expr_constLevels_x21(v___x_1798_);
lean_dec_ref(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1761_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = l_Lean_mkConst(v___x_1797_, v___x_1800_);
v___x_1802_ = l_Lean_mkAppN(v___x_1801_, v___x_1780_);
lean_dec_ref(v___x_1780_);
v___x_1803_ = l_Lean_Expr_app___override(v___x_1802_, v_a_1768_);
v___x_1804_ = l_Lean_Expr_app___override(v___x_1803_, v_x_1736_);
v___x_1805_ = l_Lean_mkAppB(v___x_1804_, v_a_1784_, v_a_1793_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1805_);
v___x_1807_ = v___x_1795_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
else
{
lean_dec(v_a_1784_);
lean_dec_ref(v___x_1780_);
lean_dec(v_a_1768_);
lean_dec(v___x_1761_);
lean_dec(v_a_1755_);
lean_dec_ref(v_x_1736_);
return v___x_1792_;
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_a_1784_);
lean_dec_ref(v___x_1780_);
lean_dec(v_a_1768_);
lean_dec_ref(v___x_1762_);
lean_dec(v___x_1761_);
lean_dec(v_a_1755_);
lean_dec(v_i_1737_);
lean_dec_ref(v_x_1736_);
lean_dec(v_u_1735_);
lean_dec_ref(v_types_1734_);
v_a_1810_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1785_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1785_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_dec_ref(v___x_1780_);
lean_dec(v_a_1768_);
lean_dec_ref(v___x_1762_);
lean_dec(v___x_1761_);
lean_dec(v_a_1755_);
lean_dec(v_i_1737_);
lean_dec_ref(v_x_1736_);
lean_dec(v_u_1735_);
lean_dec_ref(v_types_1734_);
return v___x_1783_;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_a_1768_);
lean_dec_ref(v___x_1762_);
lean_dec(v___x_1761_);
lean_dec(v_a_1755_);
lean_dec(v_i_1737_);
lean_dec_ref(v_x_1736_);
lean_dec(v_u_1735_);
lean_dec_ref(v_types_1734_);
v_a_1818_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1770_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1770_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_dec_ref(v___x_1762_);
lean_dec(v___x_1761_);
lean_dec(v_a_1755_);
lean_dec(v_i_1737_);
lean_dec_ref(v_x_1736_);
lean_dec(v_u_1735_);
lean_dec_ref(v_types_1734_);
return v___x_1767_;
}
}
}
else
{
lean_dec(v_i_1737_);
lean_dec_ref(v_x_1736_);
lean_dec(v_u_1735_);
lean_dec_ref(v_types_1734_);
return v___x_1754_;
}
}
else
{
lean_dec(v_i_1737_);
lean_dec_ref(v_x_1736_);
lean_dec(v_u_1735_);
lean_dec_ref(v_types_1734_);
return v___x_1752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object* v_i_1826_, lean_object* v___x_1827_, lean_object* v_types_1828_, lean_object* v_u_1829_, lean_object* v___x_1830_, uint8_t v___x_1831_, uint8_t v___x_1832_, uint8_t v___x_1833_, lean_object* v_x_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_nat_add(v_i_1826_, v___x_1827_);
lean_inc_ref(v_x_1834_);
v___x_1841_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1828_, v_u_1829_, v_x_1834_, v___x_1840_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = lean_array_push(v___x_1830_, v_x_1834_);
v___x_1844_ = l_Lean_Meta_mkLambdaFVars(v___x_1843_, v_a_1842_, v___x_1831_, v___x_1832_, v___x_1831_, v___x_1832_, v___x_1833_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec_ref(v___x_1843_);
return v___x_1844_;
}
else
{
lean_dec_ref(v_x_1834_);
lean_dec_ref(v___x_1830_);
return v___x_1841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object* v_types_1845_, lean_object* v_u_1846_, lean_object* v_x_1847_, lean_object* v_i_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1845_, v_u_1846_, v_x_1847_, v_i_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object* v_x_1855_, lean_object* v_body_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_Meta_getLevel(v_body_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object* v_x_1863_, lean_object* v_body_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1863_, v_body_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec_ref(v_x_1863_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object* v_types_1872_, lean_object* v_x_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___f_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; 
v___f_1879_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0));
v___x_1880_ = l_Lean_instInhabitedExpr;
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = lean_array_get_borrowed(v___x_1880_, v_types_1872_, v___x_1881_);
v___x_1883_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1884_ = 0;
lean_inc(v___x_1882_);
v___x_1885_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_1882_, v___x_1883_, v___f_1879_, v___x_1884_, v___x_1884_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1872_, v_a_1886_, v_x_1873_, v___x_1881_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
return v___x_1887_;
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v_x_1873_);
lean_dec_ref(v_types_1872_);
v_a_1888_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1885_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1885_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object* v_types_1896_, lean_object* v_x_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1896_, v_x_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object* v_a_1904_, lean_object* v___x_1905_, uint8_t v___x_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; 
lean_inc_ref(v_x_1907_);
v___x_1913_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_a_1904_, v_x_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = lean_mk_empty_array_with_capacity(v___x_1905_);
v___x_1916_ = lean_array_push(v___x_1915_, v_x_1907_);
v___x_1917_ = 1;
v___x_1918_ = 1;
v___x_1919_ = l_Lean_Meta_mkForallFVars(v___x_1916_, v_a_1914_, v___x_1906_, v___x_1917_, v___x_1917_, v___x_1918_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec_ref(v___x_1916_);
return v___x_1919_;
}
else
{
lean_dec_ref(v_x_1907_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object* v_a_1920_, lean_object* v___x_1921_, lean_object* v___x_1922_, lean_object* v_x_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
uint8_t v___x_1816__boxed_1929_; lean_object* v_res_1930_; 
v___x_1816__boxed_1929_ = lean_unbox(v___x_1922_);
v_res_1930_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1920_, v___x_1921_, v___x_1816__boxed_1929_, v_x_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___x_1921_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t v_sz_1931_, size_t v_i_1932_, lean_object* v_bs_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_usize_dec_lt(v_i_1932_, v_sz_1931_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_bs_1933_);
return v___x_1940_;
}
else
{
lean_object* v_v_1941_; lean_object* v___x_1942_; 
v_v_1941_ = lean_array_uget_borrowed(v_bs_1933_, v_i_1932_);
lean_inc(v_v_1941_);
v___x_1942_ = l_Lean_Meta_whnfForall(v_v_1941_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; lean_object* v_bs_x27_1945_; size_t v___x_1946_; size_t v___x_1947_; lean_object* v___x_1948_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = lean_unsigned_to_nat(0u);
v_bs_x27_1945_ = lean_array_uset(v_bs_1933_, v_i_1932_, v___x_1944_);
v___x_1946_ = ((size_t)1ULL);
v___x_1947_ = lean_usize_add(v_i_1932_, v___x_1946_);
v___x_1948_ = lean_array_uset(v_bs_x27_1945_, v_i_1932_, v_a_1943_);
v_i_1932_ = v___x_1947_;
v_bs_1933_ = v___x_1948_;
goto _start;
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_bs_1933_);
v_a_1950_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1942_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1942_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object* v_sz_1958_, lean_object* v_i_1959_, lean_object* v_bs_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
size_t v_sz_boxed_1966_; size_t v_i_boxed_1967_; lean_object* v_res_1968_; 
v_sz_boxed_1966_ = lean_unbox_usize(v_sz_1958_);
lean_dec(v_sz_1958_);
v_i_boxed_1967_ = lean_unbox_usize(v_i_1959_);
lean_dec(v_i_1959_);
v_res_1968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_1966_, v_i_boxed_1967_, v_bs_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1968_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0));
v___x_1971_ = l_Lean_stringToMessageData(v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object* v_as_1972_, size_t v_i_1973_, size_t v_stop_1974_, lean_object* v_b_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_a_1982_; uint8_t v___x_1986_; 
v___x_1986_ = lean_usize_dec_eq(v_i_1973_, v_stop_1974_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = lean_array_uget_borrowed(v_as_1972_, v_i_1973_);
v___x_1988_ = l_Lean_Expr_isForall(v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1989_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
lean_inc(v___x_1987_);
v___x_1990_ = l_Lean_MessageData_ofExpr(v___x_1987_);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1991_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v_a_1982_ = v_a_1993_;
goto v___jp_1981_;
}
else
{
return v___x_1992_;
}
}
else
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_box(0);
v_a_1982_ = v___x_1994_;
goto v___jp_1981_;
}
}
else
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1995_, 0, v_b_1975_);
return v___x_1995_;
}
v___jp_1981_:
{
size_t v___x_1983_; size_t v___x_1984_; 
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1973_, v___x_1983_);
v_i_1973_ = v___x_1984_;
v_b_1975_ = v_a_1982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object* v_as_1996_, lean_object* v_i_1997_, lean_object* v_stop_1998_, lean_object* v_b_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
size_t v_i_boxed_2005_; size_t v_stop_boxed_2006_; lean_object* v_res_2007_; 
v_i_boxed_2005_ = lean_unbox_usize(v_i_1997_);
lean_dec(v_i_1997_);
v_stop_boxed_2006_ = lean_unbox_usize(v_stop_1998_);
lean_dec(v_stop_1998_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_1996_, v_i_boxed_2005_, v_stop_boxed_2006_, v_b_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v_as_1996_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_bs_2010_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2011_ == 0)
{
return v_bs_2010_;
}
else
{
lean_object* v_v_2012_; lean_object* v___x_2013_; lean_object* v_bs_x27_2014_; lean_object* v___x_2015_; size_t v___x_2016_; size_t v___x_2017_; lean_object* v___x_2018_; 
v_v_2012_ = lean_array_uget(v_bs_2010_, v_i_2009_);
v___x_2013_ = lean_unsigned_to_nat(0u);
v_bs_x27_2014_ = lean_array_uset(v_bs_2010_, v_i_2009_, v___x_2013_);
v___x_2015_ = l_Lean_Expr_bindingDomain_x21(v_v_2012_);
lean_dec(v_v_2012_);
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_add(v_i_2009_, v___x_2016_);
v___x_2018_ = lean_array_uset(v_bs_x27_2014_, v_i_2009_, v___x_2015_);
v_i_2009_ = v___x_2017_;
v_bs_2010_ = v___x_2018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object* v_sz_2020_, lean_object* v_i_2021_, lean_object* v_bs_2022_){
_start:
{
size_t v_sz_boxed_2023_; size_t v_i_boxed_2024_; lean_object* v_res_2025_; 
v_sz_boxed_2023_ = lean_unbox_usize(v_sz_2020_);
lean_dec(v_sz_2020_);
v_i_boxed_2024_ = lean_unbox_usize(v_i_2021_);
lean_dec(v_i_2021_);
v_res_2025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_2023_, v_i_boxed_2024_, v_bs_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object* v_types_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2032_ = lean_array_get_size(v_types_2026_);
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_nat_dec_eq(v___x_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
size_t v_sz_2035_; size_t v___x_2036_; lean_object* v___x_2037_; 
v_sz_2035_ = lean_array_size(v_types_2026_);
v___x_2036_ = ((size_t)0ULL);
v___x_2037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2035_, v___x_2036_, v_types_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; lean_object* v___f_2040_; lean_object* v___y_2059_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_n(v_a_2038_, 2);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = lean_box(v___x_2034_);
v___f_2040_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2040_, 0, v_a_2038_);
lean_closure_set(v___f_2040_, 1, v___x_2033_);
lean_closure_set(v___f_2040_, 2, v___x_2039_);
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = lean_array_get_size(v_a_2038_);
v___x_2070_ = lean_nat_dec_lt(v___x_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
goto v___jp_2041_;
}
else
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_nat_dec_le(v___x_2069_, v___x_2069_);
if (v___x_2072_ == 0)
{
if (v___x_2070_ == 0)
{
goto v___jp_2041_;
}
else
{
size_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_usize_of_nat(v___x_2069_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2038_, v___x_2036_, v___x_2073_, v___x_2071_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
v___y_2059_ = v___x_2074_;
goto v___jp_2058_;
}
}
else
{
size_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_usize_of_nat(v___x_2069_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2038_, v___x_2036_, v___x_2075_, v___x_2071_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
v___y_2059_ = v___x_2076_;
goto v___jp_2058_;
}
}
v___jp_2041_:
{
size_t v_sz_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v_sz_2042_ = lean_array_size(v_a_2038_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_2042_, v___x_2036_, v_a_2038_);
v___x_2044_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2043_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2047_ = l_Lean_Core_mkFreshUserName(v___x_2046_, v_a_2029_, v_a_2030_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2048_, v_a_2045_, v___f_2040_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
return v___x_2049_;
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_a_2045_);
lean_dec_ref(v___f_2040_);
v_a_2050_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2047_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2047_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_dec_ref(v___f_2040_);
return v___x_2044_;
}
}
v___jp_2058_:
{
if (lean_obj_tag(v___y_2059_) == 0)
{
lean_dec_ref_known(v___y_2059_, 1);
goto v___jp_2041_;
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v___f_2040_);
lean_dec(v_a_2038_);
v_a_2060_ = lean_ctor_get(v___y_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___y_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___y_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___y_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2037_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2037_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2085_ = l_Lean_instInhabitedExpr;
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_array_get(v___x_2085_, v_types_2026_, v___x_2086_);
lean_dec_ref(v_types_2026_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object* v_types_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
return v_res_2095_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0));
v___x_2098_ = l_Lean_stringToMessageData(v___x_2097_);
return v___x_2098_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object* v___x_2102_, lean_object* v_as_2103_, size_t v_i_2104_, size_t v_stop_2105_, lean_object* v_b_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_a_2113_; uint8_t v___x_2117_; 
v___x_2117_ = lean_usize_dec_eq(v_i_2104_, v_stop_2105_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_array_uget_borrowed(v_as_2103_, v_i_2104_);
lean_inc_ref(v___x_2102_);
lean_inc(v___x_2118_);
v___x_2119_ = l_Lean_Meta_isExprDefEq(v___x_2118_, v___x_2102_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; uint8_t v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v___x_2121_ = lean_unbox(v_a_2120_);
lean_dec(v_a_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
lean_inc(v___x_2118_);
v___x_2123_ = l_Lean_MessageData_ofExpr(v___x_2118_);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
v___x_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
lean_inc_ref(v___x_2102_);
v___x_2127_ = l_Lean_MessageData_ofExpr(v___x_2102_);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2128_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v_a_2113_ = v_a_2130_;
goto v___jp_2112_;
}
else
{
lean_dec_ref(v___x_2102_);
return v___x_2129_;
}
}
else
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_box(0);
v_a_2113_ = v___x_2131_;
goto v___jp_2112_;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v___x_2102_);
v_a_2132_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2119_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2119_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v___x_2140_; 
lean_dec_ref(v___x_2102_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_b_2106_);
return v___x_2140_;
}
v___jp_2112_:
{
size_t v___x_2114_; size_t v___x_2115_; 
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2104_, v___x_2114_);
v_i_2104_ = v___x_2115_;
v_b_2106_ = v_a_2113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object* v___x_2141_, lean_object* v_as_2142_, lean_object* v_i_2143_, lean_object* v_stop_2144_, lean_object* v_b_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
size_t v_i_boxed_2151_; size_t v_stop_boxed_2152_; lean_object* v_res_2153_; 
v_i_boxed_2151_ = lean_unbox_usize(v_i_2143_);
lean_dec(v_i_2143_);
v_stop_boxed_2152_ = lean_unbox_usize(v_stop_2144_);
lean_dec(v_stop_2144_);
v_res_2153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2141_, v_as_2142_, v_i_boxed_2151_, v_stop_boxed_2152_, v_b_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec_ref(v_as_2142_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t v_sz_2154_, size_t v_i_2155_, lean_object* v_bs_2156_){
_start:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_usize_dec_lt(v_i_2155_, v_sz_2154_);
if (v___x_2157_ == 0)
{
return v_bs_2156_;
}
else
{
lean_object* v_v_2158_; lean_object* v___x_2159_; lean_object* v_bs_x27_2160_; lean_object* v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
v_v_2158_ = lean_array_uget(v_bs_2156_, v_i_2155_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v_bs_x27_2160_ = lean_array_uset(v_bs_2156_, v_i_2155_, v___x_2159_);
v___x_2161_ = l_Lean_Expr_bindingBody_x21(v_v_2158_);
lean_dec(v_v_2158_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2155_, v___x_2162_);
v___x_2164_ = lean_array_uset(v_bs_x27_2160_, v_i_2155_, v___x_2161_);
v_i_2155_ = v___x_2163_;
v_bs_2156_ = v___x_2164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object* v_sz_2166_, lean_object* v_i_2167_, lean_object* v_bs_2168_){
_start:
{
size_t v_sz_boxed_2169_; size_t v_i_boxed_2170_; lean_object* v_res_2171_; 
v_sz_boxed_2169_ = lean_unbox_usize(v_sz_2166_);
lean_dec(v_sz_2166_);
v_i_boxed_2170_ = lean_unbox_usize(v_i_2167_);
lean_dec(v_i_2167_);
v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_2169_, v_i_boxed_2170_, v_bs_2168_);
return v_res_2171_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0));
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object* v_as_2175_, size_t v_i_2176_, size_t v_stop_2177_, lean_object* v_b_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_a_2185_; uint8_t v___x_2189_; 
v___x_2189_ = lean_usize_dec_eq(v_i_2176_, v_stop_2177_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = lean_array_uget_borrowed(v_as_2175_, v_i_2176_);
v___x_2191_ = l_Lean_Expr_isArrow(v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2192_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
lean_inc(v___x_2190_);
v___x_2193_ = l_Lean_MessageData_ofExpr(v___x_2190_);
v___x_2194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2194_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
v_a_2185_ = v_a_2196_;
goto v___jp_2184_;
}
else
{
return v___x_2195_;
}
}
else
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_box(0);
v_a_2185_ = v___x_2197_;
goto v___jp_2184_;
}
}
else
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v_b_2178_);
return v___x_2198_;
}
v___jp_2184_:
{
size_t v___x_2186_; size_t v___x_2187_; 
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_add(v_i_2176_, v___x_2186_);
v_i_2176_ = v___x_2187_;
v_b_2178_ = v_a_2185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object* v_as_2199_, lean_object* v_i_2200_, lean_object* v_stop_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
size_t v_i_boxed_2208_; size_t v_stop_boxed_2209_; lean_object* v_res_2210_; 
v_i_boxed_2208_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_stop_boxed_2209_ = lean_unbox_usize(v_stop_2201_);
lean_dec(v_stop_2201_);
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2199_, v_i_boxed_2208_, v_stop_boxed_2209_, v_b_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_as_2199_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object* v_types_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
size_t v_sz_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v_sz_2217_ = lean_array_size(v_types_2211_);
v___x_2218_ = ((size_t)0ULL);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2217_, v___x_2218_, v_types_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___y_2224_; size_t v___y_2225_; lean_object* v___y_2232_; size_t v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2260_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = l_Lean_instInhabitedExpr;
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_array_get_size(v_a_2220_);
v___x_2270_ = lean_nat_dec_lt(v___x_2222_, v___x_2269_);
if (v___x_2270_ == 0)
{
goto v___jp_2243_;
}
else
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_nat_dec_le(v___x_2269_, v___x_2269_);
if (v___x_2272_ == 0)
{
if (v___x_2270_ == 0)
{
goto v___jp_2243_;
}
else
{
size_t v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_usize_of_nat(v___x_2269_);
v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2220_, v___x_2218_, v___x_2273_, v___x_2271_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
v___y_2260_ = v___x_2274_;
goto v___jp_2259_;
}
}
else
{
size_t v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_usize_of_nat(v___x_2269_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2220_, v___x_2218_, v___x_2275_, v___x_2271_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
v___y_2260_ = v___x_2276_;
goto v___jp_2259_;
}
}
v___jp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_2225_, v___x_2218_, v_a_2220_);
v___x_2227_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2226_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2229_ = lean_array_get(v___x_2221_, v___y_2224_, v___x_2222_);
lean_dec_ref(v___y_2224_);
v___x_2230_ = l_Lean_mkArrow(v_a_2228_, v___x_2229_, v_a_2214_, v_a_2215_);
return v___x_2230_;
}
else
{
lean_dec_ref(v___y_2224_);
return v___x_2227_;
}
}
v___jp_2231_:
{
if (lean_obj_tag(v___y_2234_) == 0)
{
lean_dec_ref_known(v___y_2234_, 1);
v___y_2224_ = v___y_2232_;
v___y_2225_ = v___y_2233_;
goto v___jp_2223_;
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v___y_2232_);
lean_dec(v_a_2220_);
v_a_2235_ = lean_ctor_get(v___y_2234_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___y_2234_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___y_2234_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___y_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
v___jp_2243_:
{
size_t v_sz_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_sz_2244_ = lean_array_size(v_a_2220_);
lean_inc(v_a_2220_);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2244_, v___x_2218_, v_a_2220_);
v___x_2246_ = lean_array_get_size(v___x_2245_);
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = lean_nat_sub(v___x_2246_, v___x_2247_);
v___x_2249_ = lean_array_get(v___x_2221_, v___x_2245_, v___x_2248_);
lean_dec(v___x_2248_);
lean_inc_ref(v___x_2245_);
v___x_2250_ = lean_array_pop(v___x_2245_);
v___x_2251_ = lean_array_get_size(v___x_2250_);
v___x_2252_ = lean_nat_dec_lt(v___x_2222_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_dec_ref(v___x_2250_);
lean_dec(v___x_2249_);
v___y_2224_ = v___x_2245_;
v___y_2225_ = v_sz_2244_;
goto v___jp_2223_;
}
else
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_nat_dec_le(v___x_2251_, v___x_2251_);
if (v___x_2254_ == 0)
{
if (v___x_2252_ == 0)
{
lean_dec_ref(v___x_2250_);
lean_dec(v___x_2249_);
v___y_2224_ = v___x_2245_;
v___y_2225_ = v_sz_2244_;
goto v___jp_2223_;
}
else
{
size_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_usize_of_nat(v___x_2251_);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2249_, v___x_2250_, v___x_2218_, v___x_2255_, v___x_2253_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
lean_dec_ref(v___x_2250_);
v___y_2232_ = v___x_2245_;
v___y_2233_ = v_sz_2244_;
v___y_2234_ = v___x_2256_;
goto v___jp_2231_;
}
}
else
{
size_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_usize_of_nat(v___x_2251_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2249_, v___x_2250_, v___x_2218_, v___x_2257_, v___x_2253_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
lean_dec_ref(v___x_2250_);
v___y_2232_ = v___x_2245_;
v___y_2233_ = v_sz_2244_;
v___y_2234_ = v___x_2258_;
goto v___jp_2231_;
}
}
}
v___jp_2259_:
{
if (lean_obj_tag(v___y_2260_) == 0)
{
lean_dec_ref_known(v___y_2260_, 1);
goto v___jp_2243_;
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec(v_a_2220_);
v_a_2261_ = lean_ctor_get(v___y_2260_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___y_2260_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___y_2260_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___y_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
v_a_2277_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2219_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2219_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object* v_types_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2291_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0));
v___x_2294_ = l_Lean_stringToMessageData(v___x_2293_);
return v___x_2294_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2));
v___x_2297_ = l_Lean_stringToMessageData(v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object* v___x_2298_, lean_object* v___x_2299_, lean_object* v_arg_2300_, lean_object* v_arg_2301_, lean_object* v___x_2302_, lean_object* v_a_2303_, lean_object* v_tail_2304_, lean_object* v___x_2305_, lean_object* v___x_2306_, lean_object* v___x_2307_, lean_object* v_y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v___x_2349__boxed_2314_; uint8_t v___x_2350__boxed_2315_; uint8_t v___x_2351__boxed_2316_; lean_object* v_res_2317_; 
v___x_2349__boxed_2314_ = lean_unbox(v___x_2305_);
v___x_2350__boxed_2315_ = lean_unbox(v___x_2306_);
v___x_2351__boxed_2316_ = lean_unbox(v___x_2307_);
v_res_2317_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v___x_2298_, v___x_2299_, v_arg_2300_, v_arg_2301_, v___x_2302_, v_a_2303_, v_tail_2304_, v___x_2349__boxed_2314_, v___x_2350__boxed_2315_, v___x_2351__boxed_2316_, v_y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object* v_x_2318_, lean_object* v_codomain_2319_, lean_object* v_alts_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
if (lean_obj_tag(v_alts_2320_) == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec_ref(v_codomain_2319_);
lean_dec_ref(v_x_2318_);
v___x_2326_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
v___x_2327_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2326_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
return v___x_2327_;
}
else
{
lean_object* v_tail_2328_; 
v_tail_2328_ = lean_ctor_get(v_alts_2320_, 1);
if (lean_obj_tag(v_tail_2328_) == 0)
{
lean_object* v_head_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v_codomain_2319_);
v_head_2329_ = lean_ctor_get(v_alts_2320_, 0);
lean_inc(v_head_2329_);
lean_dec_ref_known(v_alts_2320_, 2);
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_mk_empty_array_with_capacity(v___x_2330_);
v___x_2332_ = lean_array_push(v___x_2331_, v_x_2318_);
v___x_2333_ = l_Lean_Expr_beta(v_head_2329_, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
return v___x_2334_;
}
else
{
lean_object* v_head_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2420_; 
lean_inc(v_tail_2328_);
v_head_2335_ = lean_ctor_get(v_alts_2320_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_alts_2320_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v_alts_2320_, 1);
lean_dec(v_unused_2421_);
v___x_2337_ = v_alts_2320_;
v_isShared_2338_ = v_isSharedCheck_2420_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_head_2335_);
lean_dec(v_alts_2320_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2420_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; 
lean_inc(v_a_2324_);
lean_inc_ref(v_a_2323_);
lean_inc(v_a_2322_);
lean_inc_ref(v_a_2321_);
lean_inc_ref(v_x_2318_);
v___x_2339_ = lean_infer_type(v_x_2318_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc_n(v_a_2340_, 2);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2340_, v_a_2322_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2352_ = l_Lean_Expr_cleanupAnnotations(v_a_2342_);
v___x_2353_ = l_Lean_Expr_isApp(v___x_2352_);
if (v___x_2353_ == 0)
{
lean_dec_ref(v___x_2352_);
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_codomain_2319_);
lean_dec_ref(v_x_2318_);
v___y_2344_ = v_a_2321_;
v___y_2345_ = v_a_2322_;
v___y_2346_ = v_a_2323_;
v___y_2347_ = v_a_2324_;
goto v___jp_2343_;
}
else
{
lean_object* v_arg_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v_arg_2354_ = lean_ctor_get(v___x_2352_, 1);
lean_inc_ref(v_arg_2354_);
v___x_2355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2352_);
v___x_2356_ = l_Lean_Expr_isApp(v___x_2355_);
if (v___x_2356_ == 0)
{
lean_dec_ref(v___x_2355_);
lean_dec_ref(v_arg_2354_);
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_codomain_2319_);
lean_dec_ref(v_x_2318_);
v___y_2344_ = v_a_2321_;
v___y_2345_ = v_a_2322_;
v___y_2346_ = v_a_2323_;
v___y_2347_ = v_a_2324_;
goto v___jp_2343_;
}
else
{
lean_object* v_arg_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_arg_2357_ = lean_ctor_get(v___x_2355_, 1);
lean_inc_ref(v_arg_2357_);
v___x_2358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2355_);
v___x_2359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0));
v___x_2360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_2361_ = l_Lean_Expr_isConstOf(v___x_2358_, v___x_2360_);
lean_dec_ref(v___x_2358_);
if (v___x_2361_ == 0)
{
lean_dec_ref(v_arg_2357_);
lean_dec_ref(v_arg_2354_);
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_codomain_2319_);
lean_dec_ref(v_x_2318_);
v___y_2344_ = v_a_2321_;
v___y_2345_ = v_a_2322_;
v___y_2346_ = v_a_2323_;
v___y_2347_ = v_a_2324_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2362_; 
lean_inc_ref(v_codomain_2319_);
v___x_2362_ = l_Lean_Meta_getLevel(v_codomain_2319_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_mk_empty_array_with_capacity(v___x_2364_);
lean_inc_ref(v_x_2318_);
lean_inc_ref(v___x_2365_);
v___x_2366_ = lean_array_push(v___x_2365_, v_x_2318_);
v___x_2367_ = 0;
v___x_2368_ = 1;
v___x_2369_ = l_Lean_Meta_mkLambdaFVars(v___x_2366_, v_codomain_2319_, v___x_2367_, v___x_2361_, v___x_2367_, v___x_2361_, v___x_2368_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec_ref(v___x_2366_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2411_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2411_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2411_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_alt_u2082_2377_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; 
v___x_2374_ = l_Lean_Expr_getAppFn(v_a_2340_);
lean_dec(v_a_2340_);
v___x_2375_ = l_Lean_Expr_constLevels_x21(v___x_2374_);
lean_dec_ref(v___x_2374_);
v___x_2387_ = lean_box(v___x_2367_);
v___x_2388_ = lean_box(v___x_2361_);
v___x_2389_ = lean_box(v___x_2368_);
lean_inc(v_tail_2328_);
lean_inc(v_a_2370_);
lean_inc_ref(v_arg_2354_);
lean_inc_ref(v_arg_2357_);
lean_inc(v___x_2375_);
v___f_2390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2390_, 0, v___x_2359_);
lean_closure_set(v___f_2390_, 1, v___x_2375_);
lean_closure_set(v___f_2390_, 2, v_arg_2357_);
lean_closure_set(v___f_2390_, 3, v_arg_2354_);
lean_closure_set(v___f_2390_, 4, v___x_2365_);
lean_closure_set(v___f_2390_, 5, v_a_2370_);
lean_closure_set(v___f_2390_, 6, v_tail_2328_);
lean_closure_set(v___f_2390_, 7, v___x_2387_);
lean_closure_set(v___f_2390_, 8, v___x_2388_);
lean_closure_set(v___f_2390_, 9, v___x_2389_);
if (lean_obj_tag(v_tail_2328_) == 1)
{
lean_object* v_tail_2409_; 
v_tail_2409_ = lean_ctor_get(v_tail_2328_, 1);
if (lean_obj_tag(v_tail_2409_) == 0)
{
lean_object* v_head_2410_; 
lean_dec_ref(v___f_2390_);
v_head_2410_ = lean_ctor_get(v_tail_2328_, 0);
lean_inc(v_head_2410_);
lean_dec_ref_known(v_tail_2328_, 2);
v_alt_u2082_2377_ = v_head_2410_;
goto v___jp_2376_;
}
else
{
lean_dec_ref_known(v_tail_2328_, 2);
v___y_2392_ = v_a_2321_;
v___y_2393_ = v_a_2322_;
v___y_2394_ = v_a_2323_;
v___y_2395_ = v_a_2324_;
goto v___jp_2391_;
}
}
else
{
lean_dec(v_tail_2328_);
v___y_2392_ = v_a_2321_;
v___y_2393_ = v_a_2322_;
v___y_2394_ = v_a_2323_;
v___y_2395_ = v_a_2324_;
goto v___jp_2391_;
}
v___jp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2378_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___x_2375_);
lean_ctor_set(v___x_2337_, 0, v_a_2363_);
v___x_2380_ = v___x_2337_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2363_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v___x_2375_);
v___x_2380_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2381_ = l_Lean_Expr_const___override(v___x_2378_, v___x_2380_);
v___x_2382_ = l_Lean_mkApp6(v___x_2381_, v_arg_2357_, v_arg_2354_, v_a_2370_, v_x_2318_, v_head_2335_, v_alt_u2082_2377_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2382_);
v___x_2384_ = v___x_2372_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
v___jp_2391_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_2397_ = l_Lean_Core_mkFreshUserName(v___x_2396_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2397_, 1);
lean_inc_ref(v_arg_2354_);
v___x_2399_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2398_, v_arg_2354_, v___f_2390_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v_alt_u2082_2377_ = v_a_2400_;
goto v___jp_2376_;
}
else
{
lean_dec(v___x_2375_);
lean_del_object(v___x_2372_);
lean_dec(v_a_2370_);
lean_dec(v_a_2363_);
lean_dec_ref(v_arg_2357_);
lean_dec_ref(v_arg_2354_);
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec_ref(v_x_2318_);
return v___x_2399_;
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v___f_2390_);
lean_dec(v___x_2375_);
lean_del_object(v___x_2372_);
lean_dec(v_a_2370_);
lean_dec(v_a_2363_);
lean_dec_ref(v_arg_2357_);
lean_dec_ref(v_arg_2354_);
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec_ref(v_x_2318_);
v_a_2401_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2397_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2397_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2365_);
lean_dec(v_a_2363_);
lean_dec_ref(v_arg_2357_);
lean_dec_ref(v_arg_2354_);
lean_dec(v_a_2340_);
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_x_2318_);
return v___x_2369_;
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_arg_2357_);
lean_dec_ref(v_arg_2354_);
lean_dec(v_a_2340_);
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_codomain_2319_);
lean_dec_ref(v_x_2318_);
v_a_2412_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2362_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2362_);
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
}
v___jp_2343_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2348_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
v___x_2349_ = l_Lean_MessageData_ofExpr(v_a_2340_);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2350_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
return v___x_2351_;
}
}
else
{
lean_dec(v_a_2340_);
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_codomain_2319_);
lean_dec_ref(v_x_2318_);
return v___x_2341_;
}
}
else
{
lean_del_object(v___x_2337_);
lean_dec(v_head_2335_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_codomain_2319_);
lean_dec_ref(v_x_2318_);
return v___x_2339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object* v___x_2422_, lean_object* v___x_2423_, lean_object* v_arg_2424_, lean_object* v_arg_2425_, lean_object* v___x_2426_, lean_object* v_a_2427_, lean_object* v_tail_2428_, uint8_t v___x_2429_, uint8_t v___x_2430_, uint8_t v___x_2431_, lean_object* v_y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2438_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3));
v___x_2439_ = l_Lean_Name_mkStr2(v___x_2422_, v___x_2438_);
v___x_2440_ = l_Lean_Expr_const___override(v___x_2439_, v___x_2423_);
lean_inc_ref_n(v_y_2432_, 2);
v___x_2441_ = l_Lean_mkApp3(v___x_2440_, v_arg_2424_, v_arg_2425_, v_y_2432_);
lean_inc_ref(v___x_2426_);
v___x_2442_ = lean_array_push(v___x_2426_, v___x_2441_);
v___x_2443_ = l_Lean_Expr_beta(v_a_2427_, v___x_2442_);
v___x_2444_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_y_2432_, v___x_2443_, v_tail_2428_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v___x_2444_, 1);
v___x_2446_ = lean_array_push(v___x_2426_, v_y_2432_);
v___x_2447_ = l_Lean_Meta_mkLambdaFVars(v___x_2446_, v_a_2445_, v___x_2429_, v___x_2430_, v___x_2429_, v___x_2430_, v___x_2431_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec_ref(v___x_2446_);
return v___x_2447_;
}
else
{
lean_dec_ref(v_y_2432_);
lean_dec_ref(v___x_2426_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object* v_x_2448_, lean_object* v_codomain_2449_, lean_object* v_alts_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2448_, v_codomain_2449_, v_alts_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
return v_res_2456_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2458_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2459_ = lean_unsigned_to_nat(21u);
v___x_2460_ = lean_unsigned_to_nat(414u);
v___x_2461_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0));
v___x_2462_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2463_ = l_mkPanicMessageWithDecl(v___x_2462_, v___x_2461_, v___x_2460_, v___x_2459_, v___x_2458_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object* v___x_2464_, lean_object* v_es_2465_, lean_object* v_xs_2466_, lean_object* v_codomain_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = lean_array_get_size(v_xs_2466_);
v___x_2474_ = lean_nat_dec_eq(v___x_2473_, v___x_2464_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_dec_ref(v_codomain_2467_);
lean_dec_ref(v_es_2465_);
v___x_2475_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1);
v___x_2476_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2475_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v___x_2476_;
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = lean_array_fget_borrowed(v_xs_2466_, v___x_2477_);
v___x_2479_ = lean_array_to_list(v_es_2465_);
lean_inc(v___x_2478_);
v___x_2480_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2478_, v_codomain_2467_, v___x_2479_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
v___x_2482_ = lean_mk_empty_array_with_capacity(v___x_2464_);
lean_inc(v___x_2478_);
v___x_2483_ = lean_array_push(v___x_2482_, v___x_2478_);
v___x_2484_ = 0;
v___x_2485_ = 1;
v___x_2486_ = l_Lean_Meta_mkLambdaFVars(v___x_2483_, v_a_2481_, v___x_2484_, v___x_2474_, v___x_2484_, v___x_2474_, v___x_2485_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec_ref(v___x_2483_);
return v___x_2486_;
}
else
{
return v___x_2480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(lean_object* v___x_2487_, lean_object* v_es_2488_, lean_object* v_xs_2489_, lean_object* v_codomain_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(v___x_2487_, v_es_2488_, v_xs_2489_, v_codomain_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v_xs_2489_);
lean_dec(v___x_2487_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(lean_object* v_resultType_2497_, lean_object* v_es_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v___x_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; 
v___x_2504_ = lean_unsigned_to_nat(1u);
v___f_2505_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2505_, 0, v___x_2504_);
lean_closure_set(v___f_2505_, 1, v_es_2498_);
v___x_2506_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2507_ = 0;
v___x_2508_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_resultType_2497_, v___x_2506_, v___f_2505_, v___x_2507_, v___x_2507_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(lean_object* v_resultType_2509_, lean_object* v_es_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_2509_, v_es_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_bs_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_lt(v_i_2518_, v_sz_2517_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_bs_2519_);
return v___x_2526_;
}
else
{
lean_object* v_v_2527_; lean_object* v___x_2528_; 
v_v_2527_ = lean_array_uget_borrowed(v_bs_2519_, v_i_2518_);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v_v_2527_);
v___x_2528_ = lean_infer_type(v_v_2527_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v_bs_x27_2531_; size_t v___x_2532_; size_t v___x_2533_; lean_object* v___x_2534_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = lean_unsigned_to_nat(0u);
v_bs_x27_2531_ = lean_array_uset(v_bs_2519_, v_i_2518_, v___x_2530_);
v___x_2532_ = ((size_t)1ULL);
v___x_2533_ = lean_usize_add(v_i_2518_, v___x_2532_);
v___x_2534_ = lean_array_uset(v_bs_x27_2531_, v_i_2518_, v_a_2529_);
v_i_2518_ = v___x_2533_;
v_bs_2519_ = v___x_2534_;
goto _start;
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v_bs_2519_);
v_a_2536_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2528_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2528_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(lean_object* v_sz_2544_, lean_object* v_i_2545_, lean_object* v_bs_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
size_t v_sz_boxed_2552_; size_t v_i_boxed_2553_; lean_object* v_res_2554_; 
v_sz_boxed_2552_ = lean_unbox_usize(v_sz_2544_);
lean_dec(v_sz_2544_);
v_i_boxed_2553_ = lean_unbox_usize(v_i_2545_);
lean_dec(v_i_2545_);
v_res_2554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_boxed_2552_, v_i_boxed_2553_, v_bs_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry(lean_object* v_es_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
size_t v_sz_2561_; size_t v___x_2562_; lean_object* v___x_2563_; 
v_sz_2561_ = lean_array_size(v_es_2555_);
v___x_2562_ = ((size_t)0ULL);
lean_inc_ref(v_es_2555_);
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2561_, v___x_2562_, v_es_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2564_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_a_2566_, v_es_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
return v___x_2567_;
}
else
{
lean_dec_ref(v_es_2555_);
return v___x_2565_;
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec_ref(v_es_2555_);
v_a_2568_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2563_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2563_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(lean_object* v_es_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_es_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
return v_res_2582_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2584_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2585_ = lean_unsigned_to_nat(21u);
v___x_2586_ = lean_unsigned_to_nat(434u);
v___x_2587_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0));
v___x_2588_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2589_ = l_mkPanicMessageWithDecl(v___x_2588_, v___x_2587_, v___x_2586_, v___x_2585_, v___x_2584_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(lean_object* v___x_2590_, lean_object* v_es_2591_, lean_object* v_xs_2592_, lean_object* v_codomain_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = lean_array_get_size(v_xs_2592_);
v___x_2600_ = lean_nat_dec_eq(v___x_2599_, v___x_2590_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec_ref(v_codomain_2593_);
lean_dec_ref(v_es_2591_);
v___x_2601_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1);
v___x_2602_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2601_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2602_;
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = lean_array_fget_borrowed(v_xs_2592_, v___x_2603_);
v___x_2605_ = lean_array_to_list(v_es_2591_);
lean_inc(v___x_2604_);
v___x_2606_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2604_, v_codomain_2593_, v___x_2605_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = lean_mk_empty_array_with_capacity(v___x_2590_);
lean_inc(v___x_2604_);
v___x_2609_ = lean_array_push(v___x_2608_, v___x_2604_);
v___x_2610_ = 0;
v___x_2611_ = 1;
v___x_2612_ = l_Lean_Meta_mkLambdaFVars(v___x_2609_, v_a_2607_, v___x_2610_, v___x_2600_, v___x_2610_, v___x_2600_, v___x_2611_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec_ref(v___x_2609_);
return v___x_2612_;
}
else
{
return v___x_2606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object* v___x_2613_, lean_object* v_es_2614_, lean_object* v_xs_2615_, lean_object* v_codomain_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2613_, v_es_2614_, v_xs_2615_, v_codomain_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v_xs_2615_);
lean_dec(v___x_2613_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object* v_es_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
size_t v_sz_2629_; size_t v___x_2630_; lean_object* v___x_2631_; 
v_sz_2629_ = lean_array_size(v_es_2623_);
v___x_2630_ = ((size_t)0ULL);
lean_inc_ref(v_es_2623_);
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2629_, v___x_2630_, v_es_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_a_2632_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; lean_object* v___f_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2635_ = lean_unsigned_to_nat(1u);
v___f_2636_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2636_, 0, v___x_2635_);
lean_closure_set(v___f_2636_, 1, v_es_2623_);
v___x_2637_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2638_ = 0;
v___x_2639_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_2634_, v___x_2637_, v___f_2636_, v___x_2638_, v___x_2638_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
return v___x_2639_;
}
else
{
lean_dec_ref(v_es_2623_);
return v___x_2633_;
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec_ref(v_es_2623_);
v_a_2640_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2631_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2631_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object* v_es_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object* v_a_2655_, lean_object* v_domain_2656_, lean_object* v___x_2657_, lean_object* v_type_2658_, uint8_t v___x_2659_, lean_object* v_x_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = l_List_lengthTR___redArg(v_a_2655_);
lean_inc_ref(v_x_2660_);
v___x_2667_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2666_, v_domain_2656_, v___x_2657_, v_x_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___x_2666_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2669_ = lean_unsigned_to_nat(1u);
v___x_2670_ = lean_mk_empty_array_with_capacity(v___x_2669_);
lean_inc_ref(v___x_2670_);
v___x_2671_ = lean_array_push(v___x_2670_, v_a_2668_);
v___x_2672_ = l_Lean_Meta_instantiateForall(v_type_2658_, v___x_2671_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec_ref(v___x_2671_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = lean_array_push(v___x_2670_, v_x_2660_);
v___x_2675_ = 0;
v___x_2676_ = 1;
v___x_2677_ = l_Lean_Meta_mkForallFVars(v___x_2674_, v_a_2673_, v___x_2675_, v___x_2659_, v___x_2659_, v___x_2676_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec_ref(v___x_2674_);
return v___x_2677_;
}
else
{
lean_dec_ref(v___x_2670_);
lean_dec_ref(v_x_2660_);
return v___x_2672_;
}
}
else
{
lean_dec_ref(v_x_2660_);
lean_dec_ref(v_type_2658_);
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object* v_a_2678_, lean_object* v_domain_2679_, lean_object* v___x_2680_, lean_object* v_type_2681_, lean_object* v___x_2682_, lean_object* v_x_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v___x_788__boxed_2689_; lean_object* v_res_2690_; 
v___x_788__boxed_2689_ = lean_unbox(v___x_2682_);
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2678_, v_domain_2679_, v___x_2680_, v_type_2681_, v___x_788__boxed_2689_, v_x_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___x_2680_);
lean_dec(v_a_2678_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object* v_a_2691_, lean_object* v_domain_2692_, lean_object* v_type_2693_, size_t v_sz_2694_, size_t v_i_2695_, lean_object* v_bs_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_usize_dec_lt(v_i_2695_, v_sz_2694_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
lean_dec_ref(v_type_2693_);
lean_dec_ref(v_domain_2692_);
lean_dec(v_a_2691_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_bs_2696_);
return v___x_2703_;
}
else
{
lean_object* v_v_2704_; lean_object* v___x_2705_; lean_object* v_bs_x27_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_v_2704_ = lean_array_uget(v_bs_2696_, v_i_2695_);
v___x_2705_ = lean_unsigned_to_nat(0u);
v_bs_x27_2706_ = lean_array_uset(v_bs_2696_, v_i_2695_, v___x_2705_);
v___x_2707_ = lean_usize_to_nat(v_i_2695_);
v___x_2708_ = lean_box(v___x_2702_);
lean_inc_ref(v_type_2693_);
lean_inc_ref(v_domain_2692_);
lean_inc(v_a_2691_);
v___f_2709_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2709_, 0, v_a_2691_);
lean_closure_set(v___f_2709_, 1, v_domain_2692_);
lean_closure_set(v___f_2709_, 2, v___x_2707_);
lean_closure_set(v___f_2709_, 3, v_type_2693_);
lean_closure_set(v___f_2709_, 4, v___x_2708_);
v___x_2710_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2711_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_2710_, v_v_2704_, v___f_2709_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; size_t v___x_2713_; size_t v___x_2714_; lean_object* v___x_2715_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = ((size_t)1ULL);
v___x_2714_ = lean_usize_add(v_i_2695_, v___x_2713_);
v___x_2715_ = lean_array_uset(v_bs_x27_2706_, v_i_2695_, v_a_2712_);
v_i_2695_ = v___x_2714_;
v_bs_2696_ = v___x_2715_;
goto _start;
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v_bs_x27_2706_);
lean_dec_ref(v_type_2693_);
lean_dec_ref(v_domain_2692_);
lean_dec(v_a_2691_);
v_a_2717_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2711_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2711_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object* v_a_2725_, lean_object* v_domain_2726_, lean_object* v_type_2727_, lean_object* v_sz_2728_, lean_object* v_i_2729_, lean_object* v_bs_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2728_);
lean_dec(v_sz_2728_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2729_);
lean_dec(v_i_2729_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2725_, v_domain_2726_, v_type_2727_, v_sz_boxed_2736_, v_i_boxed_2737_, v_bs_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object* v_n_2739_, lean_object* v_type_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; uint8_t v___x_2766_; 
v___x_2766_ = l_Lean_Expr_isForall(v_type_2740_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
v___x_2767_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_2768_ = l_Lean_MessageData_ofExpr(v_type_2740_);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2769_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
else
{
v___y_2747_ = v_a_2741_;
v___y_2748_ = v_a_2742_;
v___y_2749_ = v_a_2743_;
v___y_2750_ = v_a_2744_;
goto v___jp_2746_;
}
v___jp_2746_:
{
lean_object* v_domain_2751_; lean_object* v___x_2752_; 
v_domain_2751_ = l_Lean_Expr_bindingDomain_x21(v_type_2740_);
lean_inc_ref(v_domain_2751_);
v___x_2752_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_2739_, v_domain_2751_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; size_t v_sz_2755_; size_t v___x_2756_; lean_object* v___x_2757_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc_n(v_a_2753_, 2);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = lean_array_mk(v_a_2753_);
v_sz_2755_ = lean_array_size(v___x_2754_);
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2753_, v_domain_2751_, v_type_2740_, v_sz_2755_, v___x_2756_, v___x_2754_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
return v___x_2757_;
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec_ref(v_domain_2751_);
lean_dec_ref(v_type_2740_);
v_a_2758_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2752_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2752_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object* v_n_2779_, lean_object* v_type_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2779_, v_type_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_n_2779_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object* v_a_2787_, lean_object* v_domain_2788_, lean_object* v_type_2789_, lean_object* v_as_2790_, size_t v_sz_2791_, size_t v_i_2792_, lean_object* v_bs_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2787_, v_domain_2788_, v_type_2789_, v_sz_2791_, v_i_2792_, v_bs_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object* v_a_2800_, lean_object* v_domain_2801_, lean_object* v_type_2802_, lean_object* v_as_2803_, lean_object* v_sz_2804_, lean_object* v_i_2805_, lean_object* v_bs_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
size_t v_sz_boxed_2812_; size_t v_i_boxed_2813_; lean_object* v_res_2814_; 
v_sz_boxed_2812_ = lean_unbox_usize(v_sz_2804_);
lean_dec(v_sz_2804_);
v_i_boxed_2813_ = lean_unbox_usize(v_i_2805_);
lean_dec(v_i_2805_);
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2800_, v_domain_2801_, v_type_2802_, v_as_2803_, v_sz_boxed_2812_, v_i_boxed_2813_, v_bs_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v_as_2803_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object* v_argsPacker_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = lean_array_get_size(v_argsPacker_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object* v_argsPacker_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_2817_);
lean_dec_ref(v_argsPacker_2817_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t v_sz_2819_, size_t v_i_2820_, lean_object* v_bs_2821_){
_start:
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_usize_dec_lt(v_i_2820_, v_sz_2819_);
if (v___x_2822_ == 0)
{
return v_bs_2821_;
}
else
{
lean_object* v_v_2823_; lean_object* v___x_2824_; lean_object* v_bs_x27_2825_; lean_object* v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v_v_2823_ = lean_array_uget(v_bs_2821_, v_i_2820_);
v___x_2824_ = lean_unsigned_to_nat(0u);
v_bs_x27_2825_ = lean_array_uset(v_bs_2821_, v_i_2820_, v___x_2824_);
v___x_2826_ = lean_array_get_size(v_v_2823_);
lean_dec(v_v_2823_);
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_add(v_i_2820_, v___x_2827_);
v___x_2829_ = lean_array_uset(v_bs_x27_2825_, v_i_2820_, v___x_2826_);
v_i_2820_ = v___x_2828_;
v_bs_2821_ = v___x_2829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object* v_sz_2831_, lean_object* v_i_2832_, lean_object* v_bs_2833_){
_start:
{
size_t v_sz_boxed_2834_; size_t v_i_boxed_2835_; lean_object* v_res_2836_; 
v_sz_boxed_2834_ = lean_unbox_usize(v_sz_2831_);
lean_dec(v_sz_2831_);
v_i_boxed_2835_ = lean_unbox_usize(v_i_2832_);
lean_dec(v_i_2832_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_2834_, v_i_boxed_2835_, v_bs_2833_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object* v_argsPacker_2837_){
_start:
{
size_t v_sz_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v_sz_2838_ = lean_array_size(v_argsPacker_2837_);
v___x_2839_ = ((size_t)0ULL);
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2838_, v___x_2839_, v_argsPacker_2837_);
return v___x_2840_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0(void){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Array_instInhabited(lean_box(0));
return v___x_2841_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object* v_argsPacker_2842_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2843_ = lean_array_get_size(v_argsPacker_2842_);
v___x_2844_ = lean_unsigned_to_nat(1u);
v___x_2845_ = lean_nat_dec_eq(v___x_2843_, v___x_2844_);
if (v___x_2845_ == 0)
{
return v___x_2845_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2846_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2847_ = lean_unsigned_to_nat(0u);
v___x_2848_ = lean_array_get_borrowed(v___x_2846_, v_argsPacker_2842_, v___x_2847_);
v___x_2849_ = lean_array_get_size(v___x_2848_);
v___x_2850_ = lean_nat_dec_eq(v___x_2849_, v___x_2844_);
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object* v_argsPacker_2851_){
_start:
{
uint8_t v_res_2852_; lean_object* v_r_2853_; 
v_res_2852_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2851_);
lean_dec_ref(v_argsPacker_2851_);
v_r_2853_ = lean_box(v_res_2852_);
return v_r_2853_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__2(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2856_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__1));
v___x_2857_ = lean_unsigned_to_nat(2u);
v___x_2858_ = lean_unsigned_to_nat(469u);
v___x_2859_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2860_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2861_ = l_mkPanicMessageWithDecl(v___x_2860_, v___x_2859_, v___x_2858_, v___x_2857_, v___x_2856_);
return v___x_2861_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__4(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2863_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__3));
v___x_2864_ = lean_unsigned_to_nat(2u);
v___x_2865_ = lean_unsigned_to_nat(470u);
v___x_2866_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2867_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2868_ = l_mkPanicMessageWithDecl(v___x_2867_, v___x_2866_, v___x_2865_, v___x_2864_, v___x_2863_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object* v_argsPacker_2869_, lean_object* v_domain_2870_, lean_object* v_fidx_2871_, lean_object* v_args_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2878_ = lean_array_get_size(v_argsPacker_2869_);
v___x_2879_ = lean_nat_dec_lt(v_fidx_2871_, v___x_2878_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec(v_fidx_2871_);
lean_dec_ref(v_domain_2870_);
v___x_2880_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__2, &l_Lean_Meta_ArgsPacker_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__2);
v___x_2881_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2880_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
return v___x_2881_;
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; uint8_t v___x_2886_; 
v___x_2882_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2883_ = lean_array_get_size(v_args_2872_);
v___x_2884_ = lean_array_get_borrowed(v___x_2882_, v_argsPacker_2869_, v_fidx_2871_);
v___x_2885_ = lean_array_get_size(v___x_2884_);
v___x_2886_ = lean_nat_dec_eq(v___x_2883_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v_fidx_2871_);
lean_dec_ref(v_domain_2870_);
v___x_2887_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__4, &l_Lean_Meta_ArgsPacker_pack___closed__4_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__4);
v___x_2888_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2887_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
return v___x_2888_;
}
else
{
lean_object* v___x_2889_; 
lean_inc_ref(v_domain_2870_);
v___x_2889_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_2878_, v_domain_2870_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = l_Lean_instInhabitedExpr;
lean_inc(v_fidx_2871_);
v___x_2892_ = l_List_get_x21Internal___redArg(v___x_2891_, v_a_2890_, v_fidx_2871_);
lean_dec(v_a_2890_);
v___x_2893_ = l_Lean_Meta_ArgsPacker_Unary_pack(v___x_2892_, v_args_2872_);
lean_dec(v___x_2892_);
v___x_2894_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2878_, v_domain_2870_, v_fidx_2871_, v___x_2893_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_);
lean_dec(v_fidx_2871_);
return v___x_2894_;
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_fidx_2871_);
lean_dec_ref(v_domain_2870_);
v_a_2895_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2889_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2889_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object* v_argsPacker_2903_, lean_object* v_domain_2904_, lean_object* v_fidx_2905_, lean_object* v_args_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2903_, v_domain_2904_, v_fidx_2905_, v_args_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec_ref(v_args_2906_);
lean_dec_ref(v_argsPacker_2903_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object* v_argsPacker_2913_, lean_object* v_e_2914_){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_array_get_size(v_argsPacker_2913_);
v___x_2916_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_2915_, v_e_2914_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_box(0);
return v___x_2917_;
}
else
{
lean_object* v_val_2918_; lean_object* v_fst_2919_; lean_object* v_snd_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2940_; 
v_val_2918_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_val_2918_);
lean_dec_ref_known(v___x_2916_, 1);
v_fst_2919_ = lean_ctor_get(v_val_2918_, 0);
v_snd_2920_ = lean_ctor_get(v_val_2918_, 1);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_val_2918_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2922_ = v_val_2918_;
v_isShared_2923_ = v_isSharedCheck_2940_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_snd_2920_);
lean_inc(v_fst_2919_);
lean_dec(v_val_2918_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2940_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2924_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2925_ = lean_array_get_borrowed(v___x_2924_, v_argsPacker_2913_, v_fst_2919_);
v___x_2926_ = lean_array_get_size(v___x_2925_);
v___x_2927_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_2926_, v_snd_2920_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v___x_2928_; 
lean_del_object(v___x_2922_);
lean_dec(v_fst_2919_);
v___x_2928_ = lean_box(0);
return v___x_2928_;
}
else
{
lean_object* v_val_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2939_; 
v_val_2929_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2931_ = v___x_2927_;
v_isShared_2932_ = v_isSharedCheck_2939_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_val_2929_);
lean_dec(v___x_2927_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2939_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v_val_2929_);
v___x_2934_ = v___x_2922_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_val_2929_);
v___x_2934_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2936_; 
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 0, v___x_2934_);
v___x_2936_ = v___x_2931_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object* v_argsPacker_2941_, lean_object* v_e_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_2941_, v_e_2942_);
lean_dec_ref(v_argsPacker_2941_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object* v_as_2944_, lean_object* v_bs_2945_, lean_object* v_i_2946_, lean_object* v_cs_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = lean_array_get_size(v_as_2944_);
v___x_2954_ = lean_nat_dec_lt(v_i_2946_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; 
lean_dec(v_i_2946_);
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_cs_2947_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = lean_array_get_size(v_bs_2945_);
v___x_2957_ = lean_nat_dec_lt(v_i_2946_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
lean_dec(v_i_2946_);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_cs_2947_);
return v___x_2958_;
}
else
{
lean_object* v_a_2959_; lean_object* v_b_2960_; lean_object* v___x_2961_; 
v_a_2959_ = lean_array_fget_borrowed(v_as_2944_, v_i_2946_);
v_b_2960_ = lean_array_fget_borrowed(v_bs_2945_, v_i_2946_);
lean_inc(v_b_2960_);
lean_inc(v_a_2959_);
v___x_2961_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_a_2959_, v_b_2960_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v___x_2963_ = lean_unsigned_to_nat(1u);
v___x_2964_ = lean_nat_add(v_i_2946_, v___x_2963_);
lean_dec(v_i_2946_);
v___x_2965_ = lean_array_push(v_cs_2947_, v_a_2962_);
v_i_2946_ = v___x_2964_;
v_cs_2947_ = v___x_2965_;
goto _start;
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v_cs_2947_);
lean_dec(v_i_2946_);
v_a_2967_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2961_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2961_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object* v_as_2975_, lean_object* v_bs_2976_, lean_object* v_i_2977_, lean_object* v_cs_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_2975_, v_bs_2976_, v_i_2977_, v_cs_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v_bs_2976_);
lean_dec_ref(v_as_2975_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object* v_argsPacker_2985_, lean_object* v_types_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = lean_unsigned_to_nat(0u);
v___x_2993_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_2994_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_argsPacker_2985_, v_types_2986_, v___x_2992_, v___x_2993_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2994_, 1);
v___x_2996_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2995_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
return v___x_2996_;
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
v_a_2997_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2994_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2994_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object* v_argsPacker_3005_, lean_object* v_types_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_3005_, v_types_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec_ref(v_types_3006_);
lean_dec_ref(v_argsPacker_3005_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object* v_as_3013_, lean_object* v_bs_3014_, lean_object* v_i_3015_, lean_object* v_cs_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = lean_array_get_size(v_as_3013_);
v___x_3023_ = lean_nat_dec_lt(v_i_3015_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_dec(v_i_3015_);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v_cs_3016_);
return v___x_3024_;
}
else
{
lean_object* v___x_3025_; uint8_t v___x_3026_; 
v___x_3025_ = lean_array_get_size(v_bs_3014_);
v___x_3026_ = lean_nat_dec_lt(v_i_3015_, v___x_3025_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; 
lean_dec(v_i_3015_);
v___x_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_cs_3016_);
return v___x_3027_;
}
else
{
lean_object* v_a_3028_; lean_object* v_b_3029_; lean_object* v___x_3030_; 
v_a_3028_ = lean_array_fget_borrowed(v_as_3013_, v_i_3015_);
v_b_3029_ = lean_array_fget_borrowed(v_bs_3014_, v_i_3015_);
lean_inc(v_b_3029_);
lean_inc(v_a_3028_);
v___x_3030_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_a_3028_, v_b_3029_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = lean_unsigned_to_nat(1u);
v___x_3033_ = lean_nat_add(v_i_3015_, v___x_3032_);
lean_dec(v_i_3015_);
v___x_3034_ = lean_array_push(v_cs_3016_, v_a_3031_);
v_i_3015_ = v___x_3033_;
v_cs_3016_ = v___x_3034_;
goto _start;
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v_cs_3016_);
lean_dec(v_i_3015_);
v_a_3036_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3030_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3030_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object* v_as_3044_, lean_object* v_bs_3045_, lean_object* v_i_3046_, lean_object* v_cs_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3044_, v_bs_3045_, v_i_3046_, v_cs_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec_ref(v_bs_3045_);
lean_dec_ref(v_as_3044_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object* v_argsPacker_3054_, lean_object* v_es_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3062_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3063_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3054_, v_es_3055_, v___x_3061_, v___x_3062_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3063_, 1);
v___x_3065_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_a_3064_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_);
return v___x_3065_;
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3066_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3063_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3063_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object* v_argsPacker_3074_, lean_object* v_es_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3074_, v_es_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec_ref(v_es_3075_);
lean_dec_ref(v_argsPacker_3074_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object* v_argsPacker_3082_, lean_object* v_resultType_3083_, lean_object* v_es_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3092_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3082_, v_es_3084_, v___x_3090_, v___x_3091_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3094_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___x_3094_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_3083_, v_a_3093_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
return v___x_3094_;
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v_resultType_3083_);
v_a_3095_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3092_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3092_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object* v_argsPacker_3103_, lean_object* v_resultType_3104_, lean_object* v_es_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3103_, v_resultType_3104_, v_es_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec_ref(v_es_3105_);
lean_dec_ref(v_argsPacker_3103_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object* v_argsPacker_3112_, lean_object* v_es_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3121_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3112_, v_es_3113_, v___x_3119_, v___x_3120_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3123_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref_known(v___x_3121_, 1);
v___x_3123_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_a_3122_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
return v___x_3123_;
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
v_a_3124_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3121_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3121_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object* v_argsPacker_3132_, lean_object* v_es_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3132_, v_es_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec_ref(v_es_3133_);
lean_dec_ref(v_argsPacker_3132_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object* v_msg_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___f_3146_; lean_object* v___x_920__overap_3147_; lean_object* v___x_3148_; 
v___f_3146_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_920__overap_3147_ = lean_panic_fn_borrowed(v___f_3146_, v_msg_3140_);
lean_inc(v___y_3144_);
lean_inc_ref(v___y_3143_);
lean_inc(v___y_3142_);
lean_inc_ref(v___y_3141_);
v___x_3148_ = lean_apply_5(v___x_920__overap_3147_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, lean_box(0));
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object* v_msg_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object* v_a_3156_, lean_object* v___x_3157_, lean_object* v_i_3158_, lean_object* v_e_3159_, lean_object* v_x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = l_List_lengthTR___redArg(v_a_3156_);
lean_inc_ref(v_x_3160_);
v___x_3167_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_3166_, v___x_3157_, v_i_3158_, v_x_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___x_3166_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; uint8_t v___x_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3167_, 1);
v___x_3169_ = lean_unsigned_to_nat(1u);
v___x_3170_ = lean_mk_empty_array_with_capacity(v___x_3169_);
lean_inc_ref(v___x_3170_);
v___x_3171_ = lean_array_push(v___x_3170_, v_x_3160_);
v___x_3172_ = lean_array_push(v___x_3170_, v_a_3168_);
v___x_3173_ = l_Lean_Expr_beta(v_e_3159_, v___x_3172_);
v___x_3174_ = 0;
v___x_3175_ = 1;
v___x_3176_ = 1;
v___x_3177_ = l_Lean_Meta_mkLambdaFVars(v___x_3171_, v___x_3173_, v___x_3174_, v___x_3175_, v___x_3174_, v___x_3175_, v___x_3176_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec_ref(v___x_3171_);
return v___x_3177_;
}
else
{
lean_dec_ref(v_x_3160_);
lean_dec_ref(v_e_3159_);
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object* v_a_3178_, lean_object* v___x_3179_, lean_object* v_i_3180_, lean_object* v_e_3181_, lean_object* v_x_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3178_, v___x_3179_, v_i_3180_, v_e_3181_, v_x_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v_i_3180_);
lean_dec(v_a_3178_);
return v_res_3188_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__0));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3194_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__3));
v___x_3195_ = lean_unsigned_to_nat(4u);
v___x_3196_ = lean_unsigned_to_nat(535u);
v___x_3197_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__2));
v___x_3198_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_3199_ = l_mkPanicMessageWithDecl(v___x_3198_, v___x_3197_, v___x_3196_, v___x_3195_, v___x_3194_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object* v_argsPacker_3200_, lean_object* v_e_3201_, lean_object* v_i_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3208_; 
lean_inc(v_a_3206_);
lean_inc_ref(v_a_3205_);
lean_inc(v_a_3204_);
lean_inc_ref(v_a_3203_);
lean_inc_ref(v_e_3201_);
v___x_3208_ = lean_infer_type(v_e_3201_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref_known(v___x_3208_, 1);
lean_inc(v_a_3206_);
lean_inc_ref(v_a_3205_);
lean_inc(v_a_3204_);
lean_inc_ref(v_a_3203_);
v___x_3210_ = lean_whnf(v_a_3209_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v_n_3227_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___x_3257_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3212_ = l_Lean_instInhabitedExpr;
v___x_3213_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v_n_3227_ = lean_array_get_size(v_argsPacker_3200_);
v___x_3257_ = l_Lean_Expr_isForall(v_a_3211_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__4, &l_Lean_Meta_ArgsPacker_curryProj___closed__4_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4);
v___x_3259_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v___x_3258_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_dec_ref_known(v___x_3259_, 1);
v___y_3229_ = v_a_3203_;
v___y_3230_ = v_a_3204_;
v___y_3231_ = v_a_3205_;
v___y_3232_ = v_a_3206_;
goto v___jp_3228_;
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_a_3211_);
lean_dec(v_i_3202_);
lean_dec_ref(v_e_3201_);
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
v___y_3229_ = v_a_3203_;
v___y_3230_ = v_a_3204_;
v___y_3231_ = v_a_3205_;
v___y_3232_ = v_a_3206_;
goto v___jp_3228_;
}
v___jp_3214_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_inc(v_i_3202_);
v___x_3221_ = l_List_get_x21Internal___redArg(v___x_3212_, v___y_3215_, v_i_3202_);
lean_dec(v___y_3215_);
v___x_3222_ = l_Lean_Expr_bindingName_x21(v_a_3211_);
lean_dec(v_a_3211_);
v___x_3223_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3222_, v___x_3221_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v___x_3225_ = lean_array_get_borrowed(v___x_3213_, v_argsPacker_3200_, v_i_3202_);
lean_dec(v_i_3202_);
lean_inc(v___x_3225_);
v___x_3226_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v___x_3225_, v_a_3224_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3226_;
}
else
{
lean_dec(v_i_3202_);
return v___x_3223_;
}
}
v___jp_3228_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = l_Lean_Expr_bindingDomain_x21(v_a_3211_);
lean_inc_ref(v___x_3233_);
v___x_3234_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_3227_, v___x_3233_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc_n(v_a_3235_, 2);
lean_dec_ref_known(v___x_3234_, 1);
lean_inc(v_i_3202_);
v___f_3236_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3236_, 0, v_a_3235_);
lean_closure_set(v___f_3236_, 1, v___x_3233_);
lean_closure_set(v___f_3236_, 2, v_i_3202_);
lean_closure_set(v___f_3236_, 3, v_e_3201_);
v___x_3237_ = l_List_lengthTR___redArg(v_a_3235_);
v___x_3238_ = lean_nat_dec_lt(v_i_3202_, v___x_3237_);
lean_dec(v___x_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec_ref(v___f_3236_);
lean_dec(v_a_3235_);
lean_dec(v_a_3211_);
lean_dec(v_i_3202_);
v___x_3239_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__1, &l_Lean_Meta_ArgsPacker_curryProj___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1);
v___x_3240_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3239_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
else
{
v___y_3215_ = v_a_3235_;
v___y_3216_ = v___f_3236_;
v___y_3217_ = v___y_3229_;
v___y_3218_ = v___y_3230_;
v___y_3219_ = v___y_3231_;
v___y_3220_ = v___y_3232_;
goto v___jp_3214_;
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v___x_3233_);
lean_dec(v_a_3211_);
lean_dec(v_i_3202_);
lean_dec_ref(v_e_3201_);
v_a_3249_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3234_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3234_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
else
{
lean_dec(v_i_3202_);
lean_dec_ref(v_e_3201_);
return v___x_3210_;
}
}
else
{
lean_dec(v_i_3202_);
lean_dec_ref(v_e_3201_);
return v___x_3208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object* v_argsPacker_3268_, lean_object* v_e_3269_, lean_object* v_i_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3268_, v_e_3269_, v_i_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
lean_dec(v_a_3272_);
lean_dec_ref(v_a_3271_);
lean_dec_ref(v_argsPacker_3268_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object* v_as_3277_, lean_object* v_bs_3278_, lean_object* v_i_3279_, lean_object* v_cs_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3286_ = lean_array_get_size(v_as_3277_);
v___x_3287_ = lean_nat_dec_lt(v_i_3279_, v___x_3286_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
lean_dec(v_i_3279_);
v___x_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3288_, 0, v_cs_3280_);
return v___x_3288_;
}
else
{
lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = lean_array_get_size(v_bs_3278_);
v___x_3290_ = lean_nat_dec_lt(v_i_3279_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; 
lean_dec(v_i_3279_);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v_cs_3280_);
return v___x_3291_;
}
else
{
lean_object* v_a_3292_; lean_object* v_b_3293_; lean_object* v___x_3294_; 
v_a_3292_ = lean_array_fget_borrowed(v_as_3277_, v_i_3279_);
v_b_3293_ = lean_array_fget_borrowed(v_bs_3278_, v_i_3279_);
lean_inc(v_b_3293_);
lean_inc(v_a_3292_);
v___x_3294_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_3292_, v_b_3293_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v___x_3296_ = lean_unsigned_to_nat(1u);
v___x_3297_ = lean_nat_add(v_i_3279_, v___x_3296_);
lean_dec(v_i_3279_);
v___x_3298_ = lean_array_push(v_cs_3280_, v_a_3295_);
v_i_3279_ = v___x_3297_;
v_cs_3280_ = v___x_3298_;
goto _start;
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec_ref(v_cs_3280_);
lean_dec(v_i_3279_);
v_a_3300_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3294_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3294_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object* v_as_3308_, lean_object* v_bs_3309_, lean_object* v_i_3310_, lean_object* v_cs_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3308_, v_bs_3309_, v_i_3310_, v_cs_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec_ref(v_bs_3309_);
lean_dec_ref(v_as_3308_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object* v_argsPacker_3318_, lean_object* v_t_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_array_get_size(v_argsPacker_3318_);
v___x_3326_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v___x_3325_, v_t_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3330_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_argsPacker_3318_, v_a_3327_, v___x_3328_, v___x_3329_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_);
lean_dec(v_a_3327_);
return v___x_3330_;
}
else
{
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object* v_argsPacker_3331_, lean_object* v_t_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3331_, v_t_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec_ref(v_argsPacker_3331_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object* v_upperBound_3339_, lean_object* v_argsPacker_3340_, lean_object* v_e_3341_, lean_object* v_a_3342_, lean_object* v_b_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
uint8_t v___x_3349_; 
v___x_3349_ = lean_nat_dec_lt(v_a_3342_, v_upperBound_3339_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; 
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3341_);
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_b_3343_);
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; 
lean_inc(v_a_3342_);
lean_inc_ref(v_e_3341_);
v___x_3351_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3340_, v_e_3341_, v_a_3342_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3351_, 1);
v___x_3353_ = lean_array_push(v_b_3343_, v_a_3352_);
v___x_3354_ = lean_unsigned_to_nat(1u);
v___x_3355_ = lean_nat_add(v_a_3342_, v___x_3354_);
lean_dec(v_a_3342_);
v_a_3342_ = v___x_3355_;
v_b_3343_ = v___x_3353_;
goto _start;
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref(v_b_3343_);
lean_dec(v_a_3342_);
lean_dec_ref(v_e_3341_);
v_a_3357_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3351_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3351_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object* v_upperBound_3365_, lean_object* v_argsPacker_3366_, lean_object* v_e_3367_, lean_object* v_a_3368_, lean_object* v_b_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3365_, v_argsPacker_3366_, v_e_3367_, v_a_3368_, v_b_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec_ref(v_argsPacker_3366_);
lean_dec(v_upperBound_3365_);
return v_res_3375_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curry___closed__0(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = lean_unsigned_to_nat(0u);
v___x_3377_ = l_Lean_Level_ofNat(v___x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object* v_argsPacker_3378_, lean_object* v_e_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v_es_3387_; lean_object* v___x_3388_; 
v___x_3385_ = lean_array_get_size(v_argsPacker_3378_);
v___x_3386_ = lean_unsigned_to_nat(0u);
v_es_3387_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3388_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_3385_, v_argsPacker_3378_, v_e_3379_, v___x_3386_, v_es_3387_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curry___closed__0, &l_Lean_Meta_ArgsPacker_curry___closed__0_once, _init_l_Lean_Meta_ArgsPacker_curry___closed__0);
v___x_3391_ = l_Lean_Meta_PProdN_mk(v___x_3390_, v_a_3389_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
return v___x_3391_;
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
v_a_3392_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3388_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3388_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object* v_argsPacker_3400_, lean_object* v_e_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3400_, v_e_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec_ref(v_argsPacker_3400_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object* v_upperBound_3408_, lean_object* v_argsPacker_3409_, lean_object* v_e_3410_, lean_object* v_inst_3411_, lean_object* v_R_3412_, lean_object* v_a_3413_, lean_object* v_b_3414_, lean_object* v_c_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3408_, v_argsPacker_3409_, v_e_3410_, v_a_3413_, v_b_3414_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object* v_upperBound_3422_, lean_object* v_argsPacker_3423_, lean_object* v_e_3424_, lean_object* v_inst_3425_, lean_object* v_R_3426_, lean_object* v_a_3427_, lean_object* v_b_3428_, lean_object* v_c_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3422_, v_argsPacker_3423_, v_e_3424_, v_inst_3425_, v_R_3426_, v_a_3427_, v_b_3428_, v_c_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec_ref(v_argsPacker_3423_);
lean_dec(v_upperBound_3422_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object* v_a_3436_, lean_object* v_argsPacker_3437_, lean_object* v_name_3438_, lean_object* v_k_3439_, lean_object* v_tail_3440_, lean_object* v_x_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3436_, v_argsPacker_3437_, v_name_3438_, v_k_3439_, v_tail_3440_, v_x_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object* v_argsPacker_3448_, lean_object* v_name_3449_, lean_object* v_k_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
if (lean_obj_tag(v_a_3451_) == 0)
{
lean_object* v___x_3458_; 
lean_dec(v_name_3449_);
lean_dec_ref(v_argsPacker_3448_);
lean_inc(v_a_3456_);
lean_inc_ref(v_a_3455_);
lean_inc(v_a_3454_);
lean_inc_ref(v_a_3453_);
v___x_3458_ = lean_apply_6(v_k_3450_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, lean_box(0));
return v___x_3458_;
}
else
{
lean_object* v_head_3459_; lean_object* v_tail_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_head_3459_ = lean_ctor_get(v_a_3451_, 0);
lean_inc(v_head_3459_);
v_tail_3460_ = lean_ctor_get(v_a_3451_, 1);
lean_inc(v_tail_3460_);
lean_dec_ref_known(v_a_3451_, 2);
lean_inc(v_name_3449_);
lean_inc_ref(v_argsPacker_3448_);
lean_inc_ref(v_a_3452_);
v___f_3461_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3461_, 0, v_a_3452_);
lean_closure_set(v___f_3461_, 1, v_argsPacker_3448_);
lean_closure_set(v___f_3461_, 2, v_name_3449_);
lean_closure_set(v___f_3461_, 3, v_k_3450_);
lean_closure_set(v___f_3461_, 4, v_tail_3460_);
v___x_3462_ = lean_array_get_size(v_argsPacker_3448_);
lean_dec_ref(v_argsPacker_3448_);
v___x_3463_ = lean_unsigned_to_nat(1u);
v___x_3464_ = lean_nat_dec_eq(v___x_3462_, v___x_3463_);
if (v___x_3464_ == 0)
{
uint8_t v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3465_ = 1;
v___x_3466_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3449_, v___x_3465_);
v___x_3467_ = lean_array_get_size(v_a_3452_);
lean_dec_ref(v_a_3452_);
v___x_3468_ = lean_nat_add(v___x_3467_, v___x_3463_);
v___x_3469_ = l_Nat_reprFast(v___x_3468_);
v___x_3470_ = lean_string_append(v___x_3466_, v___x_3469_);
lean_dec_ref(v___x_3469_);
v___x_3471_ = lean_box(0);
v___x_3472_ = l_Lean_Name_str___override(v___x_3471_, v___x_3470_);
v___x_3473_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3472_, v_head_3459_, v___f_3461_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; 
lean_dec_ref(v_a_3452_);
v___x_3474_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_3449_, v_head_3459_, v___f_3461_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3474_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object* v_a_3475_, lean_object* v_argsPacker_3476_, lean_object* v_name_3477_, lean_object* v_k_3478_, lean_object* v_tail_3479_, lean_object* v_x_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_array_push(v_a_3475_, v_x_3480_);
v___x_3487_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3476_, v_name_3477_, v_k_3478_, v_tail_3479_, v___x_3486_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object* v_argsPacker_3488_, lean_object* v_name_3489_, lean_object* v_k_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3488_, v_name_3489_, v_k_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_);
lean_dec(v_a_3496_);
lean_dec_ref(v_a_3495_);
lean_dec(v_a_3494_);
lean_dec_ref(v_a_3493_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object* v_00_u03b1_3499_, lean_object* v_argsPacker_3500_, lean_object* v_name_3501_, lean_object* v_k_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3500_, v_name_3501_, v_k_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object* v_00_u03b1_3511_, lean_object* v_argsPacker_3512_, lean_object* v_name_3513_, lean_object* v_k_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(v_00_u03b1_3511_, v_argsPacker_3512_, v_name_3513_, v_k_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object* v_argsPacker_3523_, lean_object* v_name_3524_, lean_object* v_type_3525_, lean_object* v_k_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3523_, v_type_3525_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3532_, 1);
v___x_3534_ = lean_array_to_list(v_a_3533_);
v___x_3535_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3536_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3523_, v_name_3524_, v_k_3526_, v___x_3534_, v___x_3535_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
return v___x_3536_;
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v_k_3526_);
lean_dec(v_name_3524_);
lean_dec_ref(v_argsPacker_3523_);
v_a_3537_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3532_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3532_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object* v_argsPacker_3545_, lean_object* v_name_3546_, lean_object* v_type_3547_, lean_object* v_k_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3545_, v_name_3546_, v_type_3547_, v_k_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object* v_00_u03b1_3555_, lean_object* v_argsPacker_3556_, lean_object* v_name_3557_, lean_object* v_type_3558_, lean_object* v_k_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3556_, v_name_3557_, v_type_3558_, v_k_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object* v_00_u03b1_3566_, lean_object* v_argsPacker_3567_, lean_object* v_name_3568_, lean_object* v_type_3569_, lean_object* v_k_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(v_00_u03b1_3566_, v_argsPacker_3567_, v_name_3568_, v_type_3569_, v_k_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object* v_argsPacker_3577_, lean_object* v_packedMotiveType_3578_, lean_object* v_type_3579_, lean_object* v_value_3580_, lean_object* v_k_3581_, lean_object* v_motives_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3577_, v_packedMotiveType_3578_, v_motives_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc_n(v_a_3589_, 2);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = lean_unsigned_to_nat(1u);
v___x_3591_ = lean_mk_empty_array_with_capacity(v___x_3590_);
v___x_3592_ = lean_array_push(v___x_3591_, v_a_3589_);
v___x_3593_ = l_Lean_Meta_instantiateForall(v_type_3579_, v___x_3592_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec_ref(v___x_3592_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3593_, 1);
v___x_3595_ = l_Lean_Expr_app___override(v_value_3580_, v_a_3589_);
lean_inc(v___y_3586_);
lean_inc_ref(v___y_3585_);
lean_inc(v___y_3584_);
lean_inc_ref(v___y_3583_);
v___x_3596_ = lean_apply_8(v_k_3581_, v_motives_3582_, v___x_3595_, v_a_3594_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, lean_box(0));
return v___x_3596_;
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec(v_a_3589_);
lean_dec_ref(v_motives_3582_);
lean_dec_ref(v_k_3581_);
lean_dec_ref(v_value_3580_);
v_a_3597_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3593_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3593_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec_ref(v_motives_3582_);
lean_dec_ref(v_k_3581_);
lean_dec_ref(v_value_3580_);
lean_dec_ref(v_type_3579_);
v_a_3605_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3588_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3588_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object* v_argsPacker_3613_, lean_object* v_packedMotiveType_3614_, lean_object* v_type_3615_, lean_object* v_value_3616_, lean_object* v_k_3617_, lean_object* v_motives_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3613_, v_packedMotiveType_3614_, v_type_3615_, v_value_3616_, v_k_3617_, v_motives_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v_argsPacker_3613_);
return v_res_3624_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0));
v___x_3627_ = l_Lean_stringToMessageData(v___x_3626_);
return v___x_3627_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2));
v___x_3630_ = l_Lean_stringToMessageData(v___x_3629_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object* v_argsPacker_3631_, lean_object* v_value_3632_, lean_object* v_type_3633_, lean_object* v_k_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_){
_start:
{
lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; uint8_t v___x_3669_; 
v___x_3669_ = l_Lean_Expr_isForall(v_type_3633_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref(v_k_3634_);
lean_dec_ref(v_value_3632_);
lean_dec_ref(v_argsPacker_3631_);
v___x_3670_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3);
v___x_3671_ = l_Lean_MessageData_ofExpr(v_type_3633_);
v___x_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3670_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v___x_3673_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3672_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_);
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
else
{
v___y_3650_ = v_a_3635_;
v___y_3651_ = v_a_3636_;
v___y_3652_ = v_a_3637_;
v___y_3653_ = v_a_3638_;
goto v___jp_3649_;
}
v___jp_3640_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = l_Lean_Expr_bindingName_x21(v_type_3633_);
lean_dec_ref(v_type_3633_);
v___x_3648_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3631_, v___x_3647_, v___y_3642_, v___y_3641_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
return v___x_3648_;
}
v___jp_3649_:
{
lean_object* v_packedMotiveType_3654_; lean_object* v___f_3655_; uint8_t v___x_3656_; 
v_packedMotiveType_3654_ = l_Lean_Expr_bindingDomain_x21(v_type_3633_);
lean_inc_ref(v_type_3633_);
lean_inc_ref(v_packedMotiveType_3654_);
lean_inc_ref(v_argsPacker_3631_);
v___f_3655_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3655_, 0, v_argsPacker_3631_);
lean_closure_set(v___f_3655_, 1, v_packedMotiveType_3654_);
lean_closure_set(v___f_3655_, 2, v_type_3633_);
lean_closure_set(v___f_3655_, 3, v_value_3632_);
lean_closure_set(v___f_3655_, 4, v_k_3634_);
v___x_3656_ = l_Lean_Expr_isForall(v_packedMotiveType_3654_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec_ref(v___f_3655_);
lean_dec_ref(v_type_3633_);
lean_dec_ref(v_argsPacker_3631_);
v___x_3657_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1);
v___x_3658_ = l_Lean_indentExpr(v_packedMotiveType_3654_);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3659_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
else
{
v___y_3641_ = v___f_3655_;
v___y_3642_ = v_packedMotiveType_3654_;
v___y_3643_ = v___y_3650_;
v___y_3644_ = v___y_3651_;
v___y_3645_ = v___y_3652_;
v___y_3646_ = v___y_3653_;
goto v___jp_3640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object* v_argsPacker_3682_, lean_object* v_value_3683_, lean_object* v_type_3684_, lean_object* v_k_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3682_, v_value_3683_, v_type_3684_, v_k_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_);
lean_dec(v_a_3689_);
lean_dec_ref(v_a_3688_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object* v_00_u03b1_3692_, lean_object* v_argsPacker_3693_, lean_object* v_value_3694_, lean_object* v_type_3695_, lean_object* v_k_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3693_, v_value_3694_, v_type_3695_, v_k_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object* v_00_u03b1_3703_, lean_object* v_argsPacker_3704_, lean_object* v_value_3705_, lean_object* v_type_3706_, lean_object* v_k_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_Meta_ArgsPacker_curryParam(v_00_u03b1_3703_, v_argsPacker_3704_, v_value_3705_, v_type_3706_, v_k_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
lean_dec(v_a_3711_);
lean_dec_ref(v_a_3710_);
lean_dec(v_a_3709_);
lean_dec_ref(v_a_3708_);
return v_res_3713_;
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
