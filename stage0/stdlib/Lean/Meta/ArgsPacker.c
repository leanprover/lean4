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
lean_object* v___x_646_; lean_object* v_env_647_; lean_object* v___x_648_; lean_object* v_mctx_649_; lean_object* v_lctx_650_; lean_object* v_options_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_646_ = lean_st_ref_get(v___y_644_);
v_env_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc_ref(v_env_647_);
lean_dec(v___x_646_);
v___x_648_ = lean_st_ref_get(v___y_642_);
v_mctx_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_mctx_649_);
lean_dec(v___x_648_);
v_lctx_650_ = lean_ctor_get(v___y_641_, 2);
v_options_651_ = lean_ctor_get(v___y_643_, 1);
lean_inc_ref(v_options_651_);
lean_inc_ref(v_lctx_650_);
v___x_652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_652_, 0, v_env_647_);
lean_ctor_set(v___x_652_, 1, v_mctx_649_);
lean_ctor_set(v___x_652_, 2, v_lctx_650_);
lean_ctor_set(v___x_652_, 3, v_options_651_);
v___x_653_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_msgData_640_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0___boxed(lean_object* v_msgData_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msgData_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_ref_668_; lean_object* v___x_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_ref_668_ = lean_ctor_get(v___y_665_, 4);
v___x_669_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
lean_inc(v_ref_668_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v_ref_668_);
lean_ctor_set(v___x_674_, 1, v_a_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 1);
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg___boxed(lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_685_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed(lean_object** _args){
lean_object* v___x_689_ = _args[0];
lean_object* v___x_690_ = _args[1];
lean_object* v___x_691_ = _args[2];
lean_object* v_arg_692_ = _args[3];
lean_object* v_arg_693_ = _args[4];
lean_object* v_a_694_ = _args[5];
lean_object* v_alt_695_ = _args[6];
lean_object* v_tail_696_ = _args[7];
lean_object* v_u_697_ = _args[8];
lean_object* v___x_698_ = _args[9];
lean_object* v___x_699_ = _args[10];
lean_object* v___x_700_ = _args[11];
lean_object* v_head_701_ = _args[12];
lean_object* v_x_702_ = _args[13];
lean_object* v___y_703_ = _args[14];
lean_object* v___y_704_ = _args[15];
lean_object* v___y_705_ = _args[16];
lean_object* v___y_706_ = _args[17];
lean_object* v___y_707_ = _args[18];
_start:
{
uint8_t v___x_2925__boxed_708_; uint8_t v___x_2926__boxed_709_; uint8_t v___x_2927__boxed_710_; lean_object* v_res_711_; 
v___x_2925__boxed_708_ = lean_unbox(v___x_698_);
v___x_2926__boxed_709_ = lean_unbox(v___x_699_);
v___x_2927__boxed_710_ = lean_unbox(v___x_700_);
v_res_711_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(v___x_689_, v___x_690_, v___x_691_, v_arg_692_, v_arg_693_, v_a_694_, v_alt_695_, v_tail_696_, v_u_697_, v___x_2925__boxed_708_, v___x_2926__boxed_709_, v___x_2927__boxed_710_, v_head_701_, v_x_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(lean_object* v_varNames_716_, lean_object* v_e_717_, lean_object* v_u_718_, lean_object* v_codomain_719_, lean_object* v_alt_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
if (lean_obj_tag(v_varNames_716_) == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v_codomain_719_);
lean_dec(v_u_718_);
lean_dec_ref(v_e_717_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_alt_720_);
return v___x_726_;
}
else
{
lean_object* v_tail_727_; 
v_tail_727_ = lean_ctor_get(v_varNames_716_, 1);
lean_inc(v_tail_727_);
if (lean_obj_tag(v_tail_727_) == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref_known(v_varNames_716_, 2);
lean_dec_ref(v_codomain_719_);
lean_dec(v_u_718_);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_mk_empty_array_with_capacity(v___x_728_);
v___x_730_ = lean_array_push(v___x_729_, v_e_717_);
v___x_731_ = l_Lean_Expr_beta(v_alt_720_, v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
else
{
lean_object* v_head_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_789_; 
v_head_733_ = lean_ctor_get(v_varNames_716_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v_varNames_716_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_varNames_716_, 1);
lean_dec(v_unused_790_);
v___x_735_ = v_varNames_716_;
v_isShared_736_ = v_isSharedCheck_789_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_head_733_);
lean_dec(v_varNames_716_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_789_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_head_737_; lean_object* v___x_738_; 
v_head_737_ = lean_ctor_get(v_tail_727_, 0);
lean_inc(v_head_737_);
lean_inc(v_a_724_);
lean_inc_ref(v_a_723_);
lean_inc(v_a_722_);
lean_inc_ref(v_a_721_);
lean_inc_ref(v_e_717_);
v___x_738_ = lean_infer_type(v_e_717_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_n(v_a_739_, 2);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_739_, v_a_722_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_751_ = l_Lean_Expr_cleanupAnnotations(v_a_741_);
v___x_752_ = l_Lean_Expr_isApp(v___x_751_);
if (v___x_752_ == 0)
{
lean_dec_ref(v___x_751_);
lean_dec(v_head_737_);
lean_del_object(v___x_735_);
lean_dec(v_head_733_);
lean_dec_ref_known(v_tail_727_, 2);
lean_dec_ref(v_alt_720_);
lean_dec_ref(v_codomain_719_);
lean_dec(v_u_718_);
lean_dec_ref(v_e_717_);
v___y_743_ = v_a_721_;
v___y_744_ = v_a_722_;
v___y_745_ = v_a_723_;
v___y_746_ = v_a_724_;
goto v___jp_742_;
}
else
{
lean_object* v_arg_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_arg_753_ = lean_ctor_get(v___x_751_, 1);
lean_inc_ref(v_arg_753_);
v___x_754_ = l_Lean_Expr_appFnCleanup___redArg(v___x_751_);
v___x_755_ = l_Lean_Expr_isApp(v___x_754_);
if (v___x_755_ == 0)
{
lean_dec_ref(v___x_754_);
lean_dec_ref(v_arg_753_);
lean_dec(v_head_737_);
lean_del_object(v___x_735_);
lean_dec(v_head_733_);
lean_dec_ref_known(v_tail_727_, 2);
lean_dec_ref(v_alt_720_);
lean_dec_ref(v_codomain_719_);
lean_dec(v_u_718_);
lean_dec_ref(v_e_717_);
v___y_743_ = v_a_721_;
v___y_744_ = v_a_722_;
v___y_745_ = v_a_723_;
v___y_746_ = v_a_724_;
goto v___jp_742_;
}
else
{
lean_object* v_arg_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_arg_756_ = lean_ctor_get(v___x_754_, 1);
lean_inc_ref(v_arg_756_);
v___x_757_ = l_Lean_Expr_appFnCleanup___redArg(v___x_754_);
v___x_758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0));
v___x_759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_760_ = l_Lean_Expr_isConstOf(v___x_757_, v___x_759_);
lean_dec_ref(v___x_757_);
if (v___x_760_ == 0)
{
lean_dec_ref(v_arg_756_);
lean_dec_ref(v_arg_753_);
lean_dec(v_head_737_);
lean_del_object(v___x_735_);
lean_dec_ref_known(v_tail_727_, 2);
lean_dec(v_head_733_);
lean_dec_ref(v_alt_720_);
lean_dec_ref(v_codomain_719_);
lean_dec(v_u_718_);
lean_dec_ref(v_e_717_);
v___y_743_ = v_a_721_;
v___y_744_ = v_a_722_;
v___y_745_ = v_a_723_;
v___y_746_ = v_a_724_;
goto v___jp_742_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_mk_empty_array_with_capacity(v___x_761_);
lean_inc_ref(v_e_717_);
lean_inc_ref(v___x_762_);
v___x_763_ = lean_array_push(v___x_762_, v_e_717_);
v___x_764_ = 0;
v___x_765_ = 1;
v___x_766_ = l_Lean_Meta_mkLambdaFVars(v___x_763_, v_codomain_719_, v___x_764_, v___x_760_, v___x_764_, v___x_760_, v___x_765_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec_ref(v___x_763_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___x_774_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc_n(v_a_767_, 2);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l_Lean_Expr_getAppFn(v_a_739_);
lean_dec(v_a_739_);
v___x_769_ = l_Lean_Expr_constLevels_x21(v___x_768_);
lean_dec_ref(v___x_768_);
v___x_770_ = lean_box(v___x_764_);
v___x_771_ = lean_box(v___x_760_);
v___x_772_ = lean_box(v___x_765_);
lean_inc(v_u_718_);
lean_inc_ref(v_arg_753_);
lean_inc_ref_n(v_arg_756_, 2);
lean_inc(v___x_769_);
v___f_773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed), 19, 13);
lean_closure_set(v___f_773_, 0, v___x_762_);
lean_closure_set(v___f_773_, 1, v___x_758_);
lean_closure_set(v___f_773_, 2, v___x_769_);
lean_closure_set(v___f_773_, 3, v_arg_756_);
lean_closure_set(v___f_773_, 4, v_arg_753_);
lean_closure_set(v___f_773_, 5, v_a_767_);
lean_closure_set(v___f_773_, 6, v_alt_720_);
lean_closure_set(v___f_773_, 7, v_tail_727_);
lean_closure_set(v___f_773_, 8, v_u_718_);
lean_closure_set(v___f_773_, 9, v___x_770_);
lean_closure_set(v___f_773_, 10, v___x_771_);
lean_closure_set(v___f_773_, 11, v___x_772_);
lean_closure_set(v___f_773_, 12, v_head_737_);
v___x_774_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_733_, v_arg_756_, v___f_773_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_788_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_788_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3));
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_769_);
lean_ctor_set(v___x_735_, 0, v_u_718_);
v___x_781_ = v___x_735_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_u_718_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___x_769_);
v___x_781_ = v_reuseFailAlloc_787_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = l_Lean_Expr_const___override(v___x_779_, v___x_781_);
v___x_783_ = l_Lean_mkApp5(v___x_782_, v_arg_756_, v_arg_753_, v_a_767_, v_e_717_, v_a_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_783_);
v___x_785_ = v___x_777_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_dec(v___x_769_);
lean_dec(v_a_767_);
lean_dec_ref(v_arg_756_);
lean_dec_ref(v_arg_753_);
lean_del_object(v___x_735_);
lean_dec(v_u_718_);
lean_dec_ref(v_e_717_);
return v___x_774_;
}
}
else
{
lean_dec_ref(v___x_762_);
lean_dec_ref(v_arg_756_);
lean_dec_ref(v_arg_753_);
lean_dec(v_a_739_);
lean_dec(v_head_737_);
lean_del_object(v___x_735_);
lean_dec_ref_known(v_tail_727_, 2);
lean_dec(v_head_733_);
lean_dec_ref(v_alt_720_);
lean_dec(v_u_718_);
lean_dec_ref(v_e_717_);
return v___x_766_;
}
}
}
}
v___jp_742_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_747_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1);
v___x_748_ = l_Lean_MessageData_ofExpr(v_a_739_);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_749_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
return v___x_750_;
}
}
else
{
lean_dec(v_a_739_);
lean_dec(v_head_737_);
lean_del_object(v___x_735_);
lean_dec(v_head_733_);
lean_dec_ref_known(v_tail_727_, 2);
lean_dec_ref(v_alt_720_);
lean_dec_ref(v_codomain_719_);
lean_dec(v_u_718_);
lean_dec_ref(v_e_717_);
return v___x_740_;
}
}
else
{
lean_dec(v_head_737_);
lean_del_object(v___x_735_);
lean_dec(v_head_733_);
lean_dec_ref_known(v_tail_727_, 2);
lean_dec_ref(v_alt_720_);
lean_dec_ref(v_codomain_719_);
lean_dec(v_u_718_);
lean_dec_ref(v_e_717_);
return v___x_738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(lean_object* v___x_791_, lean_object* v___x_792_, lean_object* v_arg_793_, lean_object* v_arg_794_, lean_object* v_x_795_, lean_object* v___x_796_, lean_object* v_a_797_, lean_object* v_alt_798_, lean_object* v___x_799_, lean_object* v_tail_800_, lean_object* v_u_801_, uint8_t v___x_802_, uint8_t v___x_803_, uint8_t v___x_804_, lean_object* v_y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6));
v___x_812_ = l_Lean_Name_mkStr2(v___x_791_, v___x_811_);
v___x_813_ = l_Lean_Expr_const___override(v___x_812_, v___x_792_);
lean_inc_ref_n(v_y_805_, 2);
lean_inc_ref(v_x_795_);
v___x_814_ = l_Lean_mkApp4(v___x_813_, v_arg_793_, v_arg_794_, v_x_795_, v_y_805_);
v___x_815_ = lean_array_push(v___x_796_, v___x_814_);
v___x_816_ = l_Lean_Expr_beta(v_a_797_, v___x_815_);
v___x_817_ = l_Lean_Expr_beta(v_alt_798_, v___x_799_);
v___x_818_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_tail_800_, v_y_805_, v_u_801_, v___x_816_, v___x_817_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = lean_unsigned_to_nat(2u);
v___x_821_ = lean_mk_empty_array_with_capacity(v___x_820_);
v___x_822_ = lean_array_push(v___x_821_, v_x_795_);
v___x_823_ = lean_array_push(v___x_822_, v_y_805_);
v___x_824_ = l_Lean_Meta_mkLambdaFVars(v___x_823_, v_a_819_, v___x_802_, v___x_803_, v___x_802_, v___x_803_, v___x_804_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec_ref(v___x_823_);
return v___x_824_;
}
else
{
lean_dec_ref(v_y_805_);
lean_dec_ref(v_x_795_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_825_ = _args[0];
lean_object* v___x_826_ = _args[1];
lean_object* v_arg_827_ = _args[2];
lean_object* v_arg_828_ = _args[3];
lean_object* v_x_829_ = _args[4];
lean_object* v___x_830_ = _args[5];
lean_object* v_a_831_ = _args[6];
lean_object* v_alt_832_ = _args[7];
lean_object* v___x_833_ = _args[8];
lean_object* v_tail_834_ = _args[9];
lean_object* v_u_835_ = _args[10];
lean_object* v___x_836_ = _args[11];
lean_object* v___x_837_ = _args[12];
lean_object* v___x_838_ = _args[13];
lean_object* v_y_839_ = _args[14];
lean_object* v___y_840_ = _args[15];
lean_object* v___y_841_ = _args[16];
lean_object* v___y_842_ = _args[17];
lean_object* v___y_843_ = _args[18];
lean_object* v___y_844_ = _args[19];
_start:
{
uint8_t v___x_2946__boxed_845_; uint8_t v___x_2947__boxed_846_; uint8_t v___x_2948__boxed_847_; lean_object* v_res_848_; 
v___x_2946__boxed_845_ = lean_unbox(v___x_836_);
v___x_2947__boxed_846_ = lean_unbox(v___x_837_);
v___x_2948__boxed_847_ = lean_unbox(v___x_838_);
v_res_848_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(v___x_825_, v___x_826_, v_arg_827_, v_arg_828_, v_x_829_, v___x_830_, v_a_831_, v_alt_832_, v___x_833_, v_tail_834_, v_u_835_, v___x_2946__boxed_845_, v___x_2947__boxed_846_, v___x_2948__boxed_847_, v_y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v_arg_852_, lean_object* v_arg_853_, lean_object* v_a_854_, lean_object* v_alt_855_, lean_object* v_tail_856_, lean_object* v_u_857_, uint8_t v___x_858_, uint8_t v___x_859_, uint8_t v___x_860_, lean_object* v_head_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_inc_ref(v_x_862_);
lean_inc_ref(v___x_849_);
v___x_868_ = lean_array_push(v___x_849_, v_x_862_);
v___x_869_ = lean_box(v___x_858_);
v___x_870_ = lean_box(v___x_859_);
v___x_871_ = lean_box(v___x_860_);
lean_inc_ref(v___x_868_);
lean_inc_ref(v_arg_853_);
v___f_872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed), 20, 14);
lean_closure_set(v___f_872_, 0, v___x_850_);
lean_closure_set(v___f_872_, 1, v___x_851_);
lean_closure_set(v___f_872_, 2, v_arg_852_);
lean_closure_set(v___f_872_, 3, v_arg_853_);
lean_closure_set(v___f_872_, 4, v_x_862_);
lean_closure_set(v___f_872_, 5, v___x_849_);
lean_closure_set(v___f_872_, 6, v_a_854_);
lean_closure_set(v___f_872_, 7, v_alt_855_);
lean_closure_set(v___f_872_, 8, v___x_868_);
lean_closure_set(v___f_872_, 9, v_tail_856_);
lean_closure_set(v___f_872_, 10, v_u_857_);
lean_closure_set(v___f_872_, 11, v___x_869_);
lean_closure_set(v___f_872_, 12, v___x_870_);
lean_closure_set(v___f_872_, 13, v___x_871_);
v___x_873_ = l_Lean_Expr_beta(v_arg_853_, v___x_868_);
v___x_874_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_861_, v___x_873_, v___f_872_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___boxed(lean_object* v_varNames_875_, lean_object* v_e_876_, lean_object* v_u_877_, lean_object* v_codomain_878_, lean_object* v_alt_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_varNames_875_, v_e_876_, v_u_877_, v_codomain_878_, v_alt_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(lean_object* v_00_u03b1_886_, lean_object* v_msg_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___boxed(lean_object* v_00_u03b1_894_, lean_object* v_msg_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(v_00_u03b1_894_, v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_904_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_905_ = lean_unsigned_to_nat(23u);
v___x_906_ = lean_unsigned_to_nat(180u);
v___x_907_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0));
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_909_ = l_mkPanicMessageWithDecl(v___x_908_, v___x_907_, v___x_906_, v___x_905_, v___x_904_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(lean_object* v___x_910_, lean_object* v___x_911_, lean_object* v_varNames_912_, lean_object* v_e_913_, uint8_t v___x_914_, uint8_t v___x_915_, lean_object* v_xs_916_, lean_object* v_codomain_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_array_get_size(v_xs_916_);
v___x_924_ = lean_nat_dec_eq(v___x_923_, v___x_910_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_codomain_917_);
lean_dec_ref(v_e_913_);
lean_dec_ref(v_varNames_912_);
v___x_925_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2);
v___x_926_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_925_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; 
lean_inc_ref(v_codomain_917_);
v___x_927_ = l_Lean_Meta_getLevel(v_codomain_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_927_, 1);
v___x_929_ = lean_array_fget_borrowed(v_xs_916_, v___x_911_);
v___x_930_ = lean_array_to_list(v_varNames_912_);
lean_inc(v___x_929_);
v___x_931_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v___x_930_, v___x_929_, v_a_928_, v_codomain_917_, v_e_913_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = lean_mk_empty_array_with_capacity(v___x_910_);
lean_inc(v___x_929_);
v___x_934_ = lean_array_push(v___x_933_, v___x_929_);
v___x_935_ = 1;
v___x_936_ = l_Lean_Meta_mkLambdaFVars(v___x_934_, v_a_932_, v___x_914_, v___x_915_, v___x_914_, v___x_915_, v___x_935_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec_ref(v___x_934_);
return v___x_936_;
}
else
{
return v___x_931_;
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_codomain_917_);
lean_dec_ref(v_e_913_);
lean_dec_ref(v_varNames_912_);
v_a_937_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_927_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_927_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed(lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v_varNames_947_, lean_object* v_e_948_, lean_object* v___x_949_, lean_object* v___x_950_, lean_object* v_xs_951_, lean_object* v_codomain_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v___x_798__boxed_958_; uint8_t v___x_799__boxed_959_; lean_object* v_res_960_; 
v___x_798__boxed_958_ = lean_unbox(v___x_949_);
v___x_799__boxed_959_ = lean_unbox(v___x_950_);
v_res_960_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(v___x_945_, v___x_946_, v_varNames_947_, v_e_948_, v___x_798__boxed_958_, v___x_799__boxed_959_, v_xs_951_, v_codomain_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_xs_951_);
lean_dec(v___x_946_);
lean_dec(v___x_945_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry(lean_object* v_varNames_966_, lean_object* v_e_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_973_ = lean_array_get_size(v_varNames_966_);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_nat_dec_eq(v___x_973_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc_ref(v_e_967_);
v___x_976_ = lean_infer_type(v_e_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
lean_inc_ref(v_varNames_966_);
v___x_978_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_966_, v_a_977_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = 1;
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_box(v___x_975_);
v___x_983_ = lean_box(v___x_980_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed), 13, 6);
lean_closure_set(v___f_984_, 0, v___x_981_);
lean_closure_set(v___f_984_, 1, v___x_974_);
lean_closure_set(v___f_984_, 2, v_varNames_966_);
lean_closure_set(v___f_984_, 3, v_e_967_);
lean_closure_set(v___f_984_, 4, v___x_982_);
lean_closure_set(v___f_984_, 5, v___x_983_);
v___x_985_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_986_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_979_, v___x_985_, v___f_984_, v___x_975_, v___x_975_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_986_;
}
else
{
lean_dec_ref(v_e_967_);
lean_dec_ref(v_varNames_966_);
return v___x_978_;
}
}
else
{
lean_dec_ref(v_e_967_);
lean_dec_ref(v_varNames_966_);
return v___x_976_;
}
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec_ref(v_varNames_966_);
v___x_987_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_988_ = 0;
v___x_989_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_990_ = l_Lean_mkLambda(v___x_987_, v___x_988_, v___x_989_, v_e_967_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___boxed(lean_object* v_varNames_992_, lean_object* v_e_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_varNames_992_, v_e_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_999_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_dummy_1005_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1));
v_dummy_1005_ = l_Lean_Expr_const___override(v___x_1004_, v___x_1003_);
return v_dummy_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(lean_object* v_args_1006_, lean_object* v_type_1007_, lean_object* v_packedDomain_1008_, lean_object* v_tail_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_dummy_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_dummy_1016_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1010_);
v___x_1017_ = lean_array_push(v_args_1006_, v_x_1010_);
v___x_1018_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1007_, v_packedDomain_1008_, v_dummy_1016_, v___x_1017_, v_tail_1009_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; uint8_t v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_mk_empty_array_with_capacity(v___x_1020_);
v___x_1022_ = lean_array_push(v___x_1021_, v_x_1010_);
v___x_1023_ = 0;
v___x_1024_ = 1;
v___x_1025_ = 1;
v___x_1026_ = l_Lean_Meta_mkForallFVars(v___x_1022_, v_a_1019_, v___x_1023_, v___x_1024_, v___x_1024_, v___x_1025_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec_ref(v___x_1022_);
return v___x_1026_;
}
else
{
lean_dec_ref(v_x_1010_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed(lean_object* v_args_1027_, lean_object* v_type_1028_, lean_object* v_packedDomain_1029_, lean_object* v_tail_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(v_args_1027_, v_type_1028_, v_packedDomain_1029_, v_tail_1030_, v_x_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed(lean_object* v_arg_1038_, lean_object* v_args_1039_, lean_object* v_type_1040_, lean_object* v_packedDomain_1041_, lean_object* v_tail_1042_, lean_object* v___x_1043_, lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
uint8_t v___x_724__boxed_1050_; lean_object* v_res_1051_; 
v___x_724__boxed_1050_ = lean_unbox(v___x_1043_);
v_res_1051_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(v_arg_1038_, v_args_1039_, v_type_1040_, v_packedDomain_1041_, v_tail_1042_, v___x_724__boxed_1050_, v_x_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(lean_object* v_type_1052_, lean_object* v_packedDomain_1053_, lean_object* v_domain_1054_, lean_object* v_args_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; 
if (lean_obj_tag(v_a_1056_) == 0)
{
lean_object* v_packedArg_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec_ref(v_domain_1054_);
v_packedArg_1071_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1053_, v_args_1055_);
lean_dec_ref(v_args_1055_);
lean_dec_ref(v_packedDomain_1053_);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_mk_empty_array_with_capacity(v___x_1072_);
v___x_1074_ = lean_array_push(v___x_1073_, v_packedArg_1071_);
v___x_1075_ = l_Lean_Meta_instantiateForall(v_type_1052_, v___x_1074_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec_ref(v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v_tail_1076_; 
v_tail_1076_ = lean_ctor_get(v_a_1056_, 1);
lean_inc(v_tail_1076_);
if (lean_obj_tag(v_tail_1076_) == 0)
{
lean_object* v_head_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; 
v_head_1077_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_head_1077_);
lean_dec_ref_known(v_a_1056_, 2);
v___f_1078_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1078_, 0, v_args_1055_);
lean_closure_set(v___f_1078_, 1, v_type_1052_);
lean_closure_set(v___f_1078_, 2, v_packedDomain_1053_);
lean_closure_set(v___f_1078_, 3, v_tail_1076_);
v___x_1079_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1077_, v_domain_1054_, v___f_1078_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
return v___x_1079_;
}
else
{
lean_object* v_head_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_head_1080_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_head_1080_);
lean_dec_ref_known(v_a_1056_, 2);
lean_inc_ref(v_domain_1054_);
v___x_1081_ = l_Lean_Expr_cleanupAnnotations(v_domain_1054_);
v___x_1082_ = l_Lean_Expr_isApp(v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec_ref(v___x_1081_);
lean_dec(v_head_1080_);
lean_dec(v_tail_1076_);
lean_dec_ref(v_args_1055_);
lean_dec_ref(v_packedDomain_1053_);
lean_dec_ref(v_type_1052_);
v___y_1063_ = v_a_1057_;
v___y_1064_ = v_a_1058_;
v___y_1065_ = v_a_1059_;
v___y_1066_ = v_a_1060_;
goto v___jp_1062_;
}
else
{
lean_object* v_arg_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_arg_1083_ = lean_ctor_get(v___x_1081_, 1);
lean_inc_ref(v_arg_1083_);
v___x_1084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1081_);
v___x_1085_ = l_Lean_Expr_isApp(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v___x_1084_);
lean_dec_ref(v_arg_1083_);
lean_dec(v_head_1080_);
lean_dec(v_tail_1076_);
lean_dec_ref(v_args_1055_);
lean_dec_ref(v_packedDomain_1053_);
lean_dec_ref(v_type_1052_);
v___y_1063_ = v_a_1057_;
v___y_1064_ = v_a_1058_;
v___y_1065_ = v_a_1059_;
v___y_1066_ = v_a_1060_;
goto v___jp_1062_;
}
else
{
lean_object* v_arg_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_arg_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc_ref(v_arg_1086_);
v___x_1087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1084_);
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1089_ = l_Lean_Expr_isConstOf(v___x_1087_, v___x_1088_);
lean_dec_ref(v___x_1087_);
if (v___x_1089_ == 0)
{
lean_dec_ref(v_arg_1086_);
lean_dec_ref(v_arg_1083_);
lean_dec(v_head_1080_);
lean_dec(v_tail_1076_);
lean_dec_ref(v_args_1055_);
lean_dec_ref(v_packedDomain_1053_);
lean_dec_ref(v_type_1052_);
v___y_1063_ = v_a_1057_;
v___y_1064_ = v_a_1058_;
v___y_1065_ = v_a_1059_;
v___y_1066_ = v_a_1060_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v_domain_1054_);
v___x_1090_ = lean_box(v___x_1089_);
v___f_1091_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1091_, 0, v_arg_1083_);
lean_closure_set(v___f_1091_, 1, v_args_1055_);
lean_closure_set(v___f_1091_, 2, v_type_1052_);
lean_closure_set(v___f_1091_, 3, v_packedDomain_1053_);
lean_closure_set(v___f_1091_, 4, v_tail_1076_);
lean_closure_set(v___f_1091_, 5, v___x_1090_);
v___x_1092_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1080_, v_arg_1086_, v___f_1091_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
return v___x_1092_;
}
}
}
}
}
v___jp_1062_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1);
v___x_1068_ = l_Lean_MessageData_ofExpr(v_domain_1054_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1069_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(lean_object* v_arg_1093_, lean_object* v_args_1094_, lean_object* v_type_1095_, lean_object* v_packedDomain_1096_, lean_object* v_tail_1097_, uint8_t v___x_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_mk_empty_array_with_capacity(v___x_1105_);
lean_inc_ref(v_x_1099_);
v___x_1107_ = lean_array_push(v___x_1106_, v_x_1099_);
lean_inc_ref(v___x_1107_);
v___x_1108_ = l_Lean_Expr_beta(v_arg_1093_, v___x_1107_);
v___x_1109_ = lean_array_push(v_args_1094_, v_x_1099_);
v___x_1110_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1095_, v_packedDomain_1096_, v___x_1108_, v___x_1109_, v_tail_1097_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; uint8_t v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = 0;
v___x_1113_ = 1;
v___x_1114_ = l_Lean_Meta_mkForallFVars(v___x_1107_, v_a_1111_, v___x_1112_, v___x_1098_, v___x_1098_, v___x_1113_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref(v___x_1107_);
return v___x_1114_;
}
else
{
lean_dec_ref(v___x_1107_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___boxed(lean_object* v_type_1115_, lean_object* v_packedDomain_1116_, lean_object* v_domain_1117_, lean_object* v_args_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1115_, v_packedDomain_1116_, v_domain_1117_, v_args_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
return v_res_1125_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0));
v___x_1128_ = l_Lean_stringToMessageData(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(lean_object* v_varNames_1129_, lean_object* v_type_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v___x_1145_; 
v___x_1145_ = l_Lean_Expr_isForall(v_type_1130_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_varNames_1129_);
v___x_1146_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_1147_ = l_Lean_MessageData_ofExpr(v_type_1130_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1148_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
v___y_1137_ = v_a_1131_;
v___y_1138_ = v_a_1132_;
v___y_1139_ = v_a_1133_;
v___y_1140_ = v_a_1134_;
goto v___jp_1136_;
}
v___jp_1136_:
{
lean_object* v_packedDomain_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_packedDomain_1141_ = l_Lean_Expr_bindingDomain_x21(v_type_1130_);
v___x_1142_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1143_ = lean_array_to_list(v_varNames_1129_);
lean_inc_ref(v_packedDomain_1141_);
v___x_1144_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1130_, v_packedDomain_1141_, v_packedDomain_1141_, v___x_1142_, v___x_1143_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___boxed(lean_object* v_varNames_1158_, lean_object* v_type_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_varNames_1158_, v_type_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1165_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0));
v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(lean_object* v_args_1169_, lean_object* v_e_1170_, lean_object* v_packedDomain_1171_, lean_object* v_tail_1172_, lean_object* v_x_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_dummy_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_dummy_1179_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1173_);
v___x_1180_ = lean_array_push(v_args_1169_, v_x_1173_);
v___x_1181_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1170_, v_packedDomain_1171_, v_dummy_1179_, v___x_1180_, v_tail_1172_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; uint8_t v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = lean_mk_empty_array_with_capacity(v___x_1183_);
v___x_1185_ = lean_array_push(v___x_1184_, v_x_1173_);
v___x_1186_ = 0;
v___x_1187_ = 1;
v___x_1188_ = 1;
v___x_1189_ = l_Lean_Meta_mkLambdaFVars(v___x_1185_, v_a_1182_, v___x_1186_, v___x_1187_, v___x_1186_, v___x_1187_, v___x_1188_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec_ref(v___x_1185_);
return v___x_1189_;
}
else
{
lean_dec_ref(v_x_1173_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed(lean_object* v_args_1190_, lean_object* v_e_1191_, lean_object* v_packedDomain_1192_, lean_object* v_tail_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(v_args_1190_, v_e_1191_, v_packedDomain_1192_, v_tail_1193_, v_x_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed(lean_object* v_arg_1201_, lean_object* v_args_1202_, lean_object* v_e_1203_, lean_object* v_packedDomain_1204_, lean_object* v_tail_1205_, lean_object* v___x_1206_, lean_object* v_x_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v___x_842__boxed_1213_; lean_object* v_res_1214_; 
v___x_842__boxed_1213_ = lean_unbox(v___x_1206_);
v_res_1214_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(v_arg_1201_, v_args_1202_, v_e_1203_, v_packedDomain_1204_, v_tail_1205_, v___x_842__boxed_1213_, v_x_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(lean_object* v_e_1215_, lean_object* v_packedDomain_1216_, lean_object* v_domain_1217_, lean_object* v_args_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; 
if (lean_obj_tag(v_a_1219_) == 0)
{
lean_object* v_packedArg_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec_ref(v_domain_1217_);
v_packedArg_1234_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1216_, v_args_1218_);
lean_dec_ref(v_args_1218_);
lean_dec_ref(v_packedDomain_1216_);
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_mk_empty_array_with_capacity(v___x_1235_);
v___x_1237_ = lean_array_push(v___x_1236_, v_packedArg_1234_);
v___x_1238_ = l_Lean_Expr_beta(v_e_1215_, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v_tail_1240_; 
v_tail_1240_ = lean_ctor_get(v_a_1219_, 1);
lean_inc(v_tail_1240_);
if (lean_obj_tag(v_tail_1240_) == 0)
{
lean_object* v_head_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; 
v_head_1241_ = lean_ctor_get(v_a_1219_, 0);
lean_inc(v_head_1241_);
lean_dec_ref_known(v_a_1219_, 2);
v___f_1242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1242_, 0, v_args_1218_);
lean_closure_set(v___f_1242_, 1, v_e_1215_);
lean_closure_set(v___f_1242_, 2, v_packedDomain_1216_);
lean_closure_set(v___f_1242_, 3, v_tail_1240_);
v___x_1243_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1241_, v_domain_1217_, v___f_1242_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1243_;
}
else
{
lean_object* v_head_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_head_1244_ = lean_ctor_get(v_a_1219_, 0);
lean_inc(v_head_1244_);
lean_dec_ref_known(v_a_1219_, 2);
lean_inc_ref(v_domain_1217_);
v___x_1245_ = l_Lean_Expr_cleanupAnnotations(v_domain_1217_);
v___x_1246_ = l_Lean_Expr_isApp(v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec_ref(v___x_1245_);
lean_dec(v_head_1244_);
lean_dec(v_tail_1240_);
lean_dec_ref(v_args_1218_);
lean_dec_ref(v_packedDomain_1216_);
lean_dec_ref(v_e_1215_);
v___y_1226_ = v_a_1220_;
v___y_1227_ = v_a_1221_;
v___y_1228_ = v_a_1222_;
v___y_1229_ = v_a_1223_;
goto v___jp_1225_;
}
else
{
lean_object* v_arg_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_arg_1247_ = lean_ctor_get(v___x_1245_, 1);
lean_inc_ref(v_arg_1247_);
v___x_1248_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1245_);
v___x_1249_ = l_Lean_Expr_isApp(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec_ref(v___x_1248_);
lean_dec_ref(v_arg_1247_);
lean_dec(v_head_1244_);
lean_dec(v_tail_1240_);
lean_dec_ref(v_args_1218_);
lean_dec_ref(v_packedDomain_1216_);
lean_dec_ref(v_e_1215_);
v___y_1226_ = v_a_1220_;
v___y_1227_ = v_a_1221_;
v___y_1228_ = v_a_1222_;
v___y_1229_ = v_a_1223_;
goto v___jp_1225_;
}
else
{
lean_object* v_arg_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_arg_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc_ref(v_arg_1250_);
v___x_1251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1248_);
v___x_1252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1253_ = l_Lean_Expr_isConstOf(v___x_1251_, v___x_1252_);
lean_dec_ref(v___x_1251_);
if (v___x_1253_ == 0)
{
lean_dec_ref(v_arg_1250_);
lean_dec_ref(v_arg_1247_);
lean_dec(v_head_1244_);
lean_dec(v_tail_1240_);
lean_dec_ref(v_args_1218_);
lean_dec_ref(v_packedDomain_1216_);
lean_dec_ref(v_e_1215_);
v___y_1226_ = v_a_1220_;
v___y_1227_ = v_a_1221_;
v___y_1228_ = v_a_1222_;
v___y_1229_ = v_a_1223_;
goto v___jp_1225_;
}
else
{
lean_object* v___x_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; 
lean_dec_ref(v_domain_1217_);
v___x_1254_ = lean_box(v___x_1253_);
v___f_1255_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1255_, 0, v_arg_1247_);
lean_closure_set(v___f_1255_, 1, v_args_1218_);
lean_closure_set(v___f_1255_, 2, v_e_1215_);
lean_closure_set(v___f_1255_, 3, v_packedDomain_1216_);
lean_closure_set(v___f_1255_, 4, v_tail_1240_);
lean_closure_set(v___f_1255_, 5, v___x_1254_);
v___x_1256_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1244_, v_arg_1250_, v___f_1255_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1256_;
}
}
}
}
}
v___jp_1225_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1);
v___x_1231_ = l_Lean_MessageData_ofExpr(v_domain_1217_);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1232_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(lean_object* v_arg_1257_, lean_object* v_args_1258_, lean_object* v_e_1259_, lean_object* v_packedDomain_1260_, lean_object* v_tail_1261_, uint8_t v___x_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_mk_empty_array_with_capacity(v___x_1269_);
lean_inc_ref(v_x_1263_);
v___x_1271_ = lean_array_push(v___x_1270_, v_x_1263_);
lean_inc_ref(v___x_1271_);
v___x_1272_ = l_Lean_Expr_beta(v_arg_1257_, v___x_1271_);
v___x_1273_ = lean_array_push(v_args_1258_, v_x_1263_);
v___x_1274_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1259_, v_packedDomain_1260_, v___x_1272_, v___x_1273_, v_tail_1261_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; uint8_t v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = 0;
v___x_1277_ = 1;
v___x_1278_ = l_Lean_Meta_mkLambdaFVars(v___x_1271_, v_a_1275_, v___x_1276_, v___x_1262_, v___x_1276_, v___x_1262_, v___x_1277_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec_ref(v___x_1271_);
return v___x_1278_;
}
else
{
lean_dec_ref(v___x_1271_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___boxed(lean_object* v_e_1279_, lean_object* v_packedDomain_1280_, lean_object* v_domain_1281_, lean_object* v_args_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1279_, v_packedDomain_1280_, v_domain_1281_, v_args_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
return v_res_1289_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_pack___closed__2, &l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_mk_empty_array_with_capacity(v___x_1294_);
v___x_1296_ = lean_array_push(v___x_1295_, v___x_1293_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(lean_object* v_varNames_1297_, lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = lean_array_get_size(v_varNames_1297_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_nat_dec_eq(v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_inc(v_a_1302_);
lean_inc_ref(v_a_1301_);
lean_inc(v_a_1300_);
lean_inc_ref(v_a_1299_);
lean_inc_ref(v_e_1298_);
v___x_1307_ = lean_infer_type(v_e_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = l_Lean_Meta_whnfForall(v_a_1308_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; uint8_t v___x_1320_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1320_ = l_Lean_Expr_isForall(v_a_1310_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_e_1298_);
lean_dec_ref(v_varNames_1297_);
v___x_1321_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1);
v___x_1322_ = l_Lean_MessageData_ofExpr(v_a_1310_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1323_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
v___y_1312_ = v_a_1299_;
v___y_1313_ = v_a_1300_;
v___y_1314_ = v_a_1301_;
v___y_1315_ = v_a_1302_;
goto v___jp_1311_;
}
v___jp_1311_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = l_Lean_Expr_bindingDomain_x21(v_a_1310_);
lean_dec(v_a_1310_);
v___x_1317_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1318_ = lean_array_to_list(v_varNames_1297_);
lean_inc_ref(v___x_1316_);
v___x_1319_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1298_, v___x_1316_, v___x_1316_, v___x_1317_, v___x_1318_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
return v___x_1319_;
}
}
else
{
lean_dec_ref(v_e_1298_);
lean_dec_ref(v_varNames_1297_);
return v___x_1309_;
}
}
else
{
lean_dec_ref(v_e_1298_);
lean_dec_ref(v_varNames_1297_);
return v___x_1307_;
}
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref(v_varNames_1297_);
v___x_1333_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2);
v___x_1334_ = l_Lean_Expr_beta(v_e_1298_, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___boxed(lean_object* v_varNames_1336_, lean_object* v_e_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v_varNames_1336_, v_e_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(lean_object* v_as_1347_, size_t v_sz_1348_, size_t v_i_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_usize_dec_lt(v_i_1349_, v_sz_1348_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_b_1350_);
return v___x_1357_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_a_1358_ = lean_array_uget_borrowed(v_as_1347_, v_i_1349_);
v___x_1359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1360_ = lean_unsigned_to_nat(2u);
v___x_1361_ = lean_mk_empty_array_with_capacity(v___x_1360_);
lean_inc(v_a_1358_);
v___x_1362_ = lean_array_push(v___x_1361_, v_a_1358_);
v___x_1363_ = lean_array_push(v___x_1362_, v_b_1350_);
v___x_1364_ = l_Lean_Meta_mkAppM(v___x_1359_, v___x_1363_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; size_t v___x_1366_; size_t v___x_1367_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1349_, v___x_1366_);
v_i_1349_ = v___x_1367_;
v_b_1350_ = v_a_1365_;
goto _start;
}
else
{
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___boxed(lean_object* v_as_1369_, lean_object* v_sz_1370_, lean_object* v_i_1371_, lean_object* v_b_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
size_t v_sz_boxed_1378_; size_t v_i_boxed_1379_; lean_object* v_res_1380_; 
v_sz_boxed_1378_ = lean_unbox_usize(v_sz_1370_);
lean_dec(v_sz_1370_);
v_i_boxed_1379_ = lean_unbox_usize(v_i_1371_);
lean_dec(v_i_1371_);
v_res_1380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v_as_1369_, v_sz_boxed_1378_, v_i_boxed_1379_, v_b_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec_ref(v_as_1369_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object* v_ds_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_r_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; size_t v_sz_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
v___x_1387_ = l_Lean_instInhabitedExpr;
v___x_1388_ = lean_array_get_size(v_ds_1381_);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_sub(v___x_1388_, v___x_1389_);
v_r_1391_ = lean_array_get(v___x_1387_, v_ds_1381_, v___x_1390_);
lean_dec(v___x_1390_);
v___x_1392_ = lean_array_pop(v_ds_1381_);
v___x_1393_ = l_Array_reverse___redArg(v___x_1392_);
v_sz_1394_ = lean_array_size(v___x_1393_);
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v___x_1393_, v_sz_1394_, v___x_1395_, v_r_1391_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec_ref(v___x_1393_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object* v_ds_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v_ds_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
return v_res_1403_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0));
v___x_1406_ = l_Lean_stringToMessageData(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object* v_n_1407_, lean_object* v_type_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v_zero_1423_; uint8_t v_isZero_1424_; 
v_zero_1423_ = lean_unsigned_to_nat(0u);
v_isZero_1424_ = lean_nat_dec_eq(v_n_1407_, v_zero_1423_);
if (v_isZero_1424_ == 1)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_type_1408_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
else
{
lean_object* v_one_1427_; lean_object* v_n_1428_; uint8_t v___x_1429_; 
v_one_1427_ = lean_unsigned_to_nat(1u);
v_n_1428_ = lean_nat_sub(v_n_1407_, v_one_1427_);
v___x_1429_ = lean_nat_dec_eq(v_n_1428_, v_zero_1423_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
lean_inc_ref(v_type_1408_);
v___x_1430_ = l_Lean_Expr_cleanupAnnotations(v_type_1408_);
v___x_1431_ = l_Lean_Expr_isApp(v___x_1430_);
if (v___x_1431_ == 0)
{
lean_dec_ref(v___x_1430_);
lean_dec(v_n_1428_);
v___y_1415_ = v_a_1409_;
v___y_1416_ = v_a_1410_;
v___y_1417_ = v_a_1411_;
v___y_1418_ = v_a_1412_;
goto v___jp_1414_;
}
else
{
lean_object* v_arg_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_arg_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc_ref(v_arg_1432_);
v___x_1433_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1430_);
v___x_1434_ = l_Lean_Expr_isApp(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v___x_1433_);
lean_dec_ref(v_arg_1432_);
lean_dec(v_n_1428_);
v___y_1415_ = v_a_1409_;
v___y_1416_ = v_a_1410_;
v___y_1417_ = v_a_1411_;
v___y_1418_ = v_a_1412_;
goto v___jp_1414_;
}
else
{
lean_object* v_arg_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_arg_1435_ = lean_ctor_get(v___x_1433_, 1);
lean_inc_ref(v_arg_1435_);
v___x_1436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1433_);
v___x_1437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1438_ = l_Lean_Expr_isConstOf(v___x_1436_, v___x_1437_);
lean_dec_ref(v___x_1436_);
if (v___x_1438_ == 0)
{
lean_dec_ref(v_arg_1435_);
lean_dec_ref(v_arg_1432_);
lean_dec(v_n_1428_);
v___y_1415_ = v_a_1409_;
v___y_1416_ = v_a_1410_;
v___y_1417_ = v_a_1411_;
v___y_1418_ = v_a_1412_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1439_; 
lean_dec_ref(v_type_1408_);
v___x_1439_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1428_, v_arg_1432_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_n_1428_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_arg_1435_);
lean_ctor_set(v___x_1444_, 1, v_a_1440_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_dec_ref(v_arg_1435_);
return v___x_1439_;
}
}
}
}
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec(v_n_1428_);
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_type_1408_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
v___jp_1414_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1);
v___x_1420_ = l_Lean_MessageData_ofExpr(v_type_1408_);
v___x_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v___x_1422_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1421_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object* v_n_1452_, lean_object* v_type_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1452_, v_type_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_n_1452_);
return v_res_1459_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0(void){
_start:
{
lean_object* v___x_1460_; lean_object* v_dummy_1461_; 
v___x_1460_ = lean_box(0);
v_dummy_1461_ = l_Lean_Expr_sort___override(v___x_1460_);
return v_dummy_1461_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1464_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1));
v___x_1465_ = lean_unsigned_to_nat(8u);
v___x_1466_ = lean_unsigned_to_nat(276u);
v___x_1467_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0));
v___x_1468_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1469_ = l_mkPanicMessageWithDecl(v___x_1468_, v___x_1467_, v___x_1466_, v___x_1465_, v___x_1464_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(lean_object* v_i_1478_, lean_object* v_fidx_1479_, lean_object* v_numFuncs_1480_, lean_object* v_arg_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_x_1482_) == 5)
{
lean_object* v_fn_1491_; lean_object* v_arg_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_fn_1491_ = lean_ctor_get(v_x_1482_, 0);
lean_inc_ref(v_fn_1491_);
v_arg_1492_ = lean_ctor_get(v_x_1482_, 1);
lean_inc_ref(v_arg_1492_);
lean_dec_ref_known(v_x_1482_, 2);
v___x_1493_ = lean_array_set(v_x_1483_, v_x_1484_, v_arg_1492_);
v___x_1494_ = lean_nat_sub(v_x_1484_, v___x_1490_);
lean_dec(v_x_1484_);
v_x_1482_ = v_fn_1491_;
v_x_1483_ = v___x_1493_;
v_x_1484_ = v___x_1494_;
goto _start;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
lean_dec(v_x_1484_);
v___x_1496_ = lean_array_get_size(v_x_1483_);
v___x_1497_ = lean_unsigned_to_nat(2u);
v___x_1498_ = lean_nat_dec_eq(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec_ref(v_x_1483_);
lean_dec_ref(v_x_1482_);
lean_dec_ref(v_arg_1481_);
v___x_1499_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2);
v___x_1500_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1499_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1501_ = l_Lean_instInhabitedExpr;
v___x_1502_ = lean_nat_dec_eq(v_i_1478_, v_fidx_1479_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_nat_add(v_i_1478_, v___x_1490_);
v___x_1504_ = lean_array_get(v___x_1501_, v_x_1483_, v___x_1490_);
lean_inc(v___x_1504_);
v___x_1505_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1480_, v_fidx_1479_, v_arg_1481_, v___x_1503_, v___x_1504_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___x_1503_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1519_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1519_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1519_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1510_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1511_ = l_Lean_Expr_constLevels_x21(v_x_1482_);
lean_dec_ref(v_x_1482_);
v___x_1512_ = l_Lean_mkConst(v___x_1510_, v___x_1511_);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_array_get(v___x_1501_, v_x_1483_, v___x_1513_);
lean_dec_ref(v_x_1483_);
v___x_1515_ = l_Lean_mkApp3(v___x_1512_, v___x_1514_, v___x_1504_, v_a_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1515_);
v___x_1517_ = v___x_1508_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_dec(v___x_1504_);
lean_dec_ref(v_x_1483_);
lean_dec_ref(v_x_1482_);
return v___x_1505_;
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1520_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1521_ = l_Lean_Expr_constLevels_x21(v_x_1482_);
lean_dec_ref(v_x_1482_);
v___x_1522_ = l_Lean_mkConst(v___x_1520_, v___x_1521_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_array_get(v___x_1501_, v_x_1483_, v___x_1523_);
v___x_1525_ = lean_array_get(v___x_1501_, v_x_1483_, v___x_1490_);
lean_dec_ref(v_x_1483_);
v___x_1526_ = l_Lean_mkApp3(v___x_1522_, v___x_1524_, v___x_1525_, v_arg_1481_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(lean_object* v_numFuncs_1528_, lean_object* v_fidx_1529_, lean_object* v_arg_1530_, lean_object* v_i_1531_, lean_object* v_type_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_nat_sub(v_numFuncs_1528_, v___x_1538_);
v___x_1540_ = lean_nat_dec_le(v___x_1539_, v_i_1531_);
lean_dec(v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Meta_whnfD(v_type_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v_dummy_1543_; lean_object* v_nargs_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v_dummy_1543_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
v_nargs_1544_ = l_Lean_Expr_getAppNumArgs(v_a_1542_);
lean_inc(v_nargs_1544_);
v___x_1545_ = lean_mk_array(v_nargs_1544_, v_dummy_1543_);
v___x_1546_ = lean_nat_sub(v_nargs_1544_, v___x_1538_);
lean_dec(v_nargs_1544_);
v___x_1547_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1531_, v_fidx_1529_, v_numFuncs_1528_, v_arg_1530_, v_a_1542_, v___x_1545_, v___x_1546_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
return v___x_1547_;
}
else
{
lean_dec_ref(v_arg_1530_);
return v___x_1541_;
}
}
else
{
lean_object* v___x_1548_; 
lean_dec_ref(v_type_1532_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_arg_1530_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___boxed(lean_object* v_numFuncs_1549_, lean_object* v_fidx_1550_, lean_object* v_arg_1551_, lean_object* v_i_1552_, lean_object* v_type_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1549_, v_fidx_1550_, v_arg_1551_, v_i_1552_, v_type_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_i_1552_);
lean_dec(v_fidx_1550_);
lean_dec(v_numFuncs_1549_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___boxed(lean_object* v_i_1560_, lean_object* v_fidx_1561_, lean_object* v_numFuncs_1562_, lean_object* v_arg_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1560_, v_fidx_1561_, v_numFuncs_1562_, v_arg_1563_, v_x_1564_, v_x_1565_, v_x_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v_numFuncs_1562_);
lean_dec(v_fidx_1561_);
lean_dec(v_i_1560_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object* v_numFuncs_1573_, lean_object* v_domain_1574_, lean_object* v_fidx_1575_, lean_object* v_arg_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_unsigned_to_nat(0u);
v___x_1583_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1573_, v_fidx_1575_, v_arg_1576_, v___x_1582_, v_domain_1574_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object* v_numFuncs_1584_, lean_object* v_domain_1585_, lean_object* v_fidx_1586_, lean_object* v_arg_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v_numFuncs_1584_, v_domain_1585_, v_fidx_1586_, v_arg_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_fidx_1586_);
lean_dec(v_numFuncs_1584_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(lean_object* v_numFuncs_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1632_; 
v_fst_1596_ = lean_ctor_get(v_a_1595_, 0);
v_snd_1597_ = lean_ctor_get(v_a_1595_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_a_1595_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1599_ = v_a_1595_;
v_isShared_1600_ = v_isSharedCheck_1632_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_snd_1597_);
lean_inc(v_fst_1596_);
lean_dec(v_a_1595_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1632_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1601_ = lean_unsigned_to_nat(1u);
v___x_1602_ = lean_nat_add(v_fst_1596_, v___x_1601_);
v___x_1603_ = lean_nat_dec_lt(v___x_1602_, v_numFuncs_1594_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1605_; 
lean_dec(v___x_1602_);
if (v_isShared_1600_ == 0)
{
v___x_1605_ = v___x_1599_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_fst_1596_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_snd_1597_);
v___x_1605_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1609_ = lean_unsigned_to_nat(3u);
v___x_1610_ = l_Lean_Expr_isAppOfArity(v_snd_1597_, v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
lean_dec(v___x_1602_);
v___x_1611_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1612_ = l_Lean_Expr_isAppOfArity(v_snd_1597_, v___x_1611_, v___x_1609_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_del_object(v___x_1599_);
lean_dec(v_snd_1597_);
lean_dec(v_fst_1596_);
v___x_1613_ = lean_box(0);
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1614_ = lean_unsigned_to_nat(2u);
v___x_1615_ = l_Lean_Expr_getAppNumArgs(v_snd_1597_);
v___x_1616_ = lean_nat_sub(v___x_1615_, v___x_1614_);
lean_dec(v___x_1615_);
v___x_1617_ = lean_nat_sub(v___x_1616_, v___x_1601_);
lean_dec(v___x_1616_);
v___x_1618_ = l_Lean_Expr_getRevArg_x21(v_snd_1597_, v___x_1617_);
lean_dec(v_snd_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 1, v___x_1618_);
v___x_1620_ = v___x_1599_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_fst_1596_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec(v_fst_1596_);
v___x_1623_ = lean_unsigned_to_nat(2u);
v___x_1624_ = l_Lean_Expr_getAppNumArgs(v_snd_1597_);
v___x_1625_ = lean_nat_sub(v___x_1624_, v___x_1623_);
lean_dec(v___x_1624_);
v___x_1626_ = lean_nat_sub(v___x_1625_, v___x_1601_);
lean_dec(v___x_1625_);
v___x_1627_ = l_Lean_Expr_getRevArg_x21(v_snd_1597_, v___x_1626_);
lean_dec(v_snd_1597_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 1, v___x_1627_);
lean_ctor_set(v___x_1599_, 0, v___x_1602_);
v___x_1629_ = v___x_1599_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
v_a_1595_ = v___x_1629_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg___boxed(lean_object* v_numFuncs_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1633_, v_a_1634_);
lean_dec(v_numFuncs_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object* v_numFuncs_1636_, lean_object* v_expr_1637_){
_start:
{
lean_object* v_funidx_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_funidx_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_funidx_1638_);
lean_ctor_set(v___x_1639_, 1, v_expr_1637_);
v___x_1640_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1636_, v___x_1639_);
if (lean_obj_tag(v___x_1640_) == 0)
{
return v___x_1640_;
}
else
{
lean_object* v_val_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1657_; 
v_val_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1657_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_val_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1657_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_fst_1645_; lean_object* v_snd_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1656_; 
v_fst_1645_ = lean_ctor_get(v_val_1641_, 0);
v_snd_1646_ = lean_ctor_get(v_val_1641_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_val_1641_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1648_ = v_val_1641_;
v_isShared_1649_ = v_isSharedCheck_1656_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snd_1646_);
lean_inc(v_fst_1645_);
lean_dec(v_val_1641_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1656_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_fst_1645_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_snd_1646_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1651_);
v___x_1653_ = v___x_1643_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(lean_object* v_numFuncs_1658_, lean_object* v_expr_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v_numFuncs_1658_, v_expr_1659_);
lean_dec(v_numFuncs_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(lean_object* v_numFuncs_1661_, lean_object* v_inst_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1661_, v_a_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(lean_object* v_numFuncs_1665_, lean_object* v_inst_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(v_numFuncs_1665_, v_inst_1666_, v_a_1667_);
lean_dec(v_numFuncs_1665_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object* v___x_1669_, lean_object* v___x_1670_, lean_object* v_types_1671_, lean_object* v_i_1672_, uint8_t v___x_1673_, uint8_t v___x_1674_, uint8_t v___x_1675_, lean_object* v_x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_inc_ref(v_x_1676_);
v___x_1682_ = lean_array_push(v___x_1669_, v_x_1676_);
v___x_1683_ = lean_array_get_borrowed(v___x_1670_, v_types_1671_, v_i_1672_);
v___x_1684_ = l_Lean_Expr_bindingBody_x21(v___x_1683_);
v___x_1685_ = lean_expr_instantiate1(v___x_1684_, v_x_1676_);
lean_dec_ref(v_x_1676_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l_Lean_Meta_mkLambdaFVars(v___x_1682_, v___x_1685_, v___x_1673_, v___x_1674_, v___x_1673_, v___x_1674_, v___x_1675_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec_ref(v___x_1682_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object* v___x_1687_, lean_object* v___x_1688_, lean_object* v_types_1689_, lean_object* v_i_1690_, lean_object* v___x_1691_, lean_object* v___x_1692_, lean_object* v___x_1693_, lean_object* v_x_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v___x_1663__boxed_1700_; uint8_t v___x_1664__boxed_1701_; uint8_t v___x_1665__boxed_1702_; lean_object* v_res_1703_; 
v___x_1663__boxed_1700_ = lean_unbox(v___x_1691_);
v___x_1664__boxed_1701_ = lean_unbox(v___x_1692_);
v___x_1665__boxed_1702_ = lean_unbox(v___x_1693_);
v_res_1703_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v___x_1687_, v___x_1688_, v_types_1689_, v_i_1690_, v___x_1663__boxed_1700_, v___x_1664__boxed_1701_, v___x_1665__boxed_1702_, v_x_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v_i_1690_);
lean_dec_ref(v_types_1689_);
lean_dec_ref(v___x_1688_);
return v_res_1703_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1706_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1));
v___x_1707_ = lean_unsigned_to_nat(6u);
v___x_1708_ = lean_unsigned_to_nat(318u);
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0));
v___x_1710_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1711_ = l_mkPanicMessageWithDecl(v___x_1710_, v___x_1709_, v___x_1708_, v___x_1707_, v___x_1706_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object* v_i_1712_, lean_object* v___x_1713_, lean_object* v_types_1714_, lean_object* v_u_1715_, lean_object* v___x_1716_, lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v___x_1723__boxed_1726_; uint8_t v___x_1724__boxed_1727_; uint8_t v___x_1725__boxed_1728_; lean_object* v_res_1729_; 
v___x_1723__boxed_1726_ = lean_unbox(v___x_1717_);
v___x_1724__boxed_1727_ = lean_unbox(v___x_1718_);
v___x_1725__boxed_1728_ = lean_unbox(v___x_1719_);
v_res_1729_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_i_1712_, v___x_1713_, v_types_1714_, v_u_1715_, v___x_1716_, v___x_1723__boxed_1726_, v___x_1724__boxed_1727_, v___x_1725__boxed_1728_, v_x_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___x_1713_);
lean_dec(v_i_1712_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object* v_types_1733_, lean_object* v_u_1734_, lean_object* v_x_1735_, lean_object* v_i_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1742_ = l_Lean_instInhabitedExpr;
v___x_1743_ = lean_array_get_size(v_types_1733_);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_sub(v___x_1743_, v___x_1744_);
v___x_1746_ = lean_nat_dec_lt(v_i_1736_, v___x_1745_);
lean_dec(v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v_u_1734_);
v___x_1747_ = lean_array_get(v___x_1742_, v_types_1733_, v_i_1736_);
lean_dec(v_i_1736_);
lean_dec_ref(v_types_1733_);
v___x_1748_ = l_Lean_Expr_bindingBody_x21(v___x_1747_);
lean_dec(v___x_1747_);
v___x_1749_ = lean_expr_instantiate1(v___x_1748_, v_x_1735_);
lean_dec_ref(v_x_1735_);
lean_dec_ref(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; 
lean_inc(v_a_1740_);
lean_inc_ref(v_a_1739_);
lean_inc(v_a_1738_);
lean_inc_ref(v_a_1737_);
lean_inc_ref(v_x_1735_);
v___x_1751_ = lean_infer_type(v_x_1735_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = l_Lean_Meta_whnfD(v_a_1752_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1756_ = lean_unsigned_to_nat(2u);
v___x_1757_ = l_Lean_Expr_isAppOfArity(v_a_1754_, v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec(v_a_1754_);
lean_dec(v_i_1736_);
lean_dec_ref(v_x_1735_);
lean_dec(v_u_1734_);
lean_dec_ref(v_types_1733_);
v___x_1758_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
v___x_1759_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1758_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; 
lean_inc_n(v_u_1734_, 2);
v___x_1760_ = l_Lean_Level_succ___override(v_u_1734_);
v___x_1761_ = lean_mk_empty_array_with_capacity(v___x_1744_);
lean_inc_ref(v_x_1735_);
lean_inc_ref(v___x_1761_);
v___x_1762_ = lean_array_push(v___x_1761_, v_x_1735_);
v___x_1763_ = l_Lean_mkSort(v_u_1734_);
v___x_1764_ = 0;
v___x_1765_ = 1;
v___x_1766_ = l_Lean_Meta_mkLambdaFVars(v___x_1762_, v___x_1763_, v___x_1764_, v___x_1746_, v___x_1764_, v___x_1746_, v___x_1765_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
lean_dec_ref(v___x_1762_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_1769_ = l_Lean_Core_mkFreshUserName(v___x_1768_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v_nargs_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___f_1775_; lean_object* v_dummy_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v_nargs_1771_ = l_Lean_Expr_getAppNumArgs(v_a_1754_);
v___x_1772_ = lean_box(v___x_1764_);
v___x_1773_ = lean_box(v___x_1746_);
v___x_1774_ = lean_box(v___x_1765_);
lean_inc(v_i_1736_);
lean_inc_ref(v_types_1733_);
lean_inc_ref(v___x_1761_);
v___f_1775_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1775_, 0, v___x_1761_);
lean_closure_set(v___f_1775_, 1, v___x_1742_);
lean_closure_set(v___f_1775_, 2, v_types_1733_);
lean_closure_set(v___f_1775_, 3, v_i_1736_);
lean_closure_set(v___f_1775_, 4, v___x_1772_);
lean_closure_set(v___f_1775_, 5, v___x_1773_);
lean_closure_set(v___f_1775_, 6, v___x_1774_);
v_dummy_1776_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
lean_inc(v_nargs_1771_);
v___x_1777_ = lean_mk_array(v_nargs_1771_, v_dummy_1776_);
v___x_1778_ = lean_nat_sub(v_nargs_1771_, v___x_1744_);
lean_dec(v_nargs_1771_);
lean_inc(v_a_1754_);
v___x_1779_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1754_, v___x_1777_, v___x_1778_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = lean_array_get_borrowed(v___x_1742_, v___x_1779_, v___x_1780_);
lean_inc(v___x_1781_);
v___x_1782_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1770_, v___x_1781_, v___f_1775_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l_Lean_Core_mkFreshUserName(v___x_1768_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___f_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = lean_box(v___x_1764_);
v___x_1787_ = lean_box(v___x_1746_);
v___x_1788_ = lean_box(v___x_1765_);
v___f_1789_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1789_, 0, v_i_1736_);
lean_closure_set(v___f_1789_, 1, v___x_1744_);
lean_closure_set(v___f_1789_, 2, v_types_1733_);
lean_closure_set(v___f_1789_, 3, v_u_1734_);
lean_closure_set(v___f_1789_, 4, v___x_1761_);
lean_closure_set(v___f_1789_, 5, v___x_1786_);
lean_closure_set(v___f_1789_, 6, v___x_1787_);
lean_closure_set(v___f_1789_, 7, v___x_1788_);
v___x_1790_ = lean_array_get(v___x_1742_, v___x_1779_, v___x_1744_);
v___x_1791_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1785_, v___x_1790_, v___f_1789_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1808_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
v___x_1797_ = l_Lean_Expr_getAppFn(v_a_1754_);
lean_dec(v_a_1754_);
v___x_1798_ = l_Lean_Expr_constLevels_x21(v___x_1797_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1760_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_Lean_mkConst(v___x_1796_, v___x_1799_);
v___x_1801_ = l_Lean_mkAppN(v___x_1800_, v___x_1779_);
lean_dec_ref(v___x_1779_);
v___x_1802_ = l_Lean_Expr_app___override(v___x_1801_, v_a_1767_);
v___x_1803_ = l_Lean_Expr_app___override(v___x_1802_, v_x_1735_);
v___x_1804_ = l_Lean_mkAppB(v___x_1803_, v_a_1783_, v_a_1792_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1804_);
v___x_1806_ = v___x_1794_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
lean_dec(v_a_1783_);
lean_dec_ref(v___x_1779_);
lean_dec(v_a_1767_);
lean_dec(v___x_1760_);
lean_dec(v_a_1754_);
lean_dec_ref(v_x_1735_);
return v___x_1791_;
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_a_1783_);
lean_dec_ref(v___x_1779_);
lean_dec(v_a_1767_);
lean_dec_ref(v___x_1761_);
lean_dec(v___x_1760_);
lean_dec(v_a_1754_);
lean_dec(v_i_1736_);
lean_dec_ref(v_x_1735_);
lean_dec(v_u_1734_);
lean_dec_ref(v_types_1733_);
v_a_1809_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1784_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1784_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_dec_ref(v___x_1779_);
lean_dec(v_a_1767_);
lean_dec_ref(v___x_1761_);
lean_dec(v___x_1760_);
lean_dec(v_a_1754_);
lean_dec(v_i_1736_);
lean_dec_ref(v_x_1735_);
lean_dec(v_u_1734_);
lean_dec_ref(v_types_1733_);
return v___x_1782_;
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_a_1767_);
lean_dec_ref(v___x_1761_);
lean_dec(v___x_1760_);
lean_dec(v_a_1754_);
lean_dec(v_i_1736_);
lean_dec_ref(v_x_1735_);
lean_dec(v_u_1734_);
lean_dec_ref(v_types_1733_);
v_a_1817_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1769_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1769_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_dec_ref(v___x_1761_);
lean_dec(v___x_1760_);
lean_dec(v_a_1754_);
lean_dec(v_i_1736_);
lean_dec_ref(v_x_1735_);
lean_dec(v_u_1734_);
lean_dec_ref(v_types_1733_);
return v___x_1766_;
}
}
}
else
{
lean_dec(v_i_1736_);
lean_dec_ref(v_x_1735_);
lean_dec(v_u_1734_);
lean_dec_ref(v_types_1733_);
return v___x_1753_;
}
}
else
{
lean_dec(v_i_1736_);
lean_dec_ref(v_x_1735_);
lean_dec(v_u_1734_);
lean_dec_ref(v_types_1733_);
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object* v_i_1825_, lean_object* v___x_1826_, lean_object* v_types_1827_, lean_object* v_u_1828_, lean_object* v___x_1829_, uint8_t v___x_1830_, uint8_t v___x_1831_, uint8_t v___x_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_nat_add(v_i_1825_, v___x_1826_);
lean_inc_ref(v_x_1833_);
v___x_1840_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1827_, v_u_1828_, v_x_1833_, v___x_1839_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = lean_array_push(v___x_1829_, v_x_1833_);
v___x_1843_ = l_Lean_Meta_mkLambdaFVars(v___x_1842_, v_a_1841_, v___x_1830_, v___x_1831_, v___x_1830_, v___x_1831_, v___x_1832_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec_ref(v___x_1842_);
return v___x_1843_;
}
else
{
lean_dec_ref(v_x_1833_);
lean_dec_ref(v___x_1829_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object* v_types_1844_, lean_object* v_u_1845_, lean_object* v_x_1846_, lean_object* v_i_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1844_, v_u_1845_, v_x_1846_, v_i_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object* v_x_1854_, lean_object* v_body_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Meta_getLevel(v_body_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object* v_x_1862_, lean_object* v_body_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1862_, v_body_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v_x_1862_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object* v_types_1871_, lean_object* v_x_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v___f_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; 
v___f_1878_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0));
v___x_1879_ = l_Lean_instInhabitedExpr;
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = lean_array_get_borrowed(v___x_1879_, v_types_1871_, v___x_1880_);
v___x_1882_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1883_ = 0;
lean_inc(v___x_1881_);
v___x_1884_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_1881_, v___x_1882_, v___f_1878_, v___x_1883_, v___x_1883_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1886_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1871_, v_a_1885_, v_x_1872_, v___x_1880_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
return v___x_1886_;
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v_x_1872_);
lean_dec_ref(v_types_1871_);
v_a_1887_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1884_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1884_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object* v_types_1895_, lean_object* v_x_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1895_, v_x_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object* v_a_1903_, lean_object* v___x_1904_, uint8_t v___x_1905_, lean_object* v_x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
lean_inc_ref(v_x_1906_);
v___x_1912_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_a_1903_, v_x_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = lean_mk_empty_array_with_capacity(v___x_1904_);
v___x_1915_ = lean_array_push(v___x_1914_, v_x_1906_);
v___x_1916_ = 1;
v___x_1917_ = 1;
v___x_1918_ = l_Lean_Meta_mkForallFVars(v___x_1915_, v_a_1913_, v___x_1905_, v___x_1916_, v___x_1916_, v___x_1917_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec_ref(v___x_1915_);
return v___x_1918_;
}
else
{
lean_dec_ref(v_x_1906_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object* v_a_1919_, lean_object* v___x_1920_, lean_object* v___x_1921_, lean_object* v_x_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
uint8_t v___x_1816__boxed_1928_; lean_object* v_res_1929_; 
v___x_1816__boxed_1928_ = lean_unbox(v___x_1921_);
v_res_1929_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1919_, v___x_1920_, v___x_1816__boxed_1928_, v_x_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___x_1920_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t v_sz_1930_, size_t v_i_1931_, lean_object* v_bs_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_usize_dec_lt(v_i_1931_, v_sz_1930_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_bs_1932_);
return v___x_1939_;
}
else
{
lean_object* v_v_1940_; lean_object* v___x_1941_; 
v_v_1940_ = lean_array_uget_borrowed(v_bs_1932_, v_i_1931_);
lean_inc(v_v_1940_);
v___x_1941_ = l_Lean_Meta_whnfForall(v_v_1940_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1943_; lean_object* v_bs_x27_1944_; size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1943_ = lean_unsigned_to_nat(0u);
v_bs_x27_1944_ = lean_array_uset(v_bs_1932_, v_i_1931_, v___x_1943_);
v___x_1945_ = ((size_t)1ULL);
v___x_1946_ = lean_usize_add(v_i_1931_, v___x_1945_);
v___x_1947_ = lean_array_uset(v_bs_x27_1944_, v_i_1931_, v_a_1942_);
v_i_1931_ = v___x_1946_;
v_bs_1932_ = v___x_1947_;
goto _start;
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_bs_1932_);
v_a_1949_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1941_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1941_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object* v_sz_1957_, lean_object* v_i_1958_, lean_object* v_bs_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
size_t v_sz_boxed_1965_; size_t v_i_boxed_1966_; lean_object* v_res_1967_; 
v_sz_boxed_1965_ = lean_unbox_usize(v_sz_1957_);
lean_dec(v_sz_1957_);
v_i_boxed_1966_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_1965_, v_i_boxed_1966_, v_bs_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
return v_res_1967_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0));
v___x_1970_ = l_Lean_stringToMessageData(v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object* v_as_1971_, size_t v_i_1972_, size_t v_stop_1973_, lean_object* v_b_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_a_1981_; uint8_t v___x_1985_; 
v___x_1985_ = lean_usize_dec_eq(v_i_1972_, v_stop_1973_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = lean_array_uget_borrowed(v_as_1971_, v_i_1972_);
v___x_1987_ = l_Lean_Expr_isForall(v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1988_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
lean_inc(v___x_1986_);
v___x_1989_ = l_Lean_MessageData_ofExpr(v___x_1986_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1990_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v_a_1981_ = v_a_1992_;
goto v___jp_1980_;
}
else
{
return v___x_1991_;
}
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_box(0);
v_a_1981_ = v___x_1993_;
goto v___jp_1980_;
}
}
else
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_b_1974_);
return v___x_1994_;
}
v___jp_1980_:
{
size_t v___x_1982_; size_t v___x_1983_; 
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_add(v_i_1972_, v___x_1982_);
v_i_1972_ = v___x_1983_;
v_b_1974_ = v_a_1981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object* v_as_1995_, lean_object* v_i_1996_, lean_object* v_stop_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
size_t v_i_boxed_2004_; size_t v_stop_boxed_2005_; lean_object* v_res_2006_; 
v_i_boxed_2004_ = lean_unbox_usize(v_i_1996_);
lean_dec(v_i_1996_);
v_stop_boxed_2005_ = lean_unbox_usize(v_stop_1997_);
lean_dec(v_stop_1997_);
v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_1995_, v_i_boxed_2004_, v_stop_boxed_2005_, v_b_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v_as_1995_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t v_sz_2007_, size_t v_i_2008_, lean_object* v_bs_2009_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_usize_dec_lt(v_i_2008_, v_sz_2007_);
if (v___x_2010_ == 0)
{
return v_bs_2009_;
}
else
{
lean_object* v_v_2011_; lean_object* v___x_2012_; lean_object* v_bs_x27_2013_; lean_object* v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; lean_object* v___x_2017_; 
v_v_2011_ = lean_array_uget(v_bs_2009_, v_i_2008_);
v___x_2012_ = lean_unsigned_to_nat(0u);
v_bs_x27_2013_ = lean_array_uset(v_bs_2009_, v_i_2008_, v___x_2012_);
v___x_2014_ = l_Lean_Expr_bindingDomain_x21(v_v_2011_);
lean_dec(v_v_2011_);
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = lean_usize_add(v_i_2008_, v___x_2015_);
v___x_2017_ = lean_array_uset(v_bs_x27_2013_, v_i_2008_, v___x_2014_);
v_i_2008_ = v___x_2016_;
v_bs_2009_ = v___x_2017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object* v_sz_2019_, lean_object* v_i_2020_, lean_object* v_bs_2021_){
_start:
{
size_t v_sz_boxed_2022_; size_t v_i_boxed_2023_; lean_object* v_res_2024_; 
v_sz_boxed_2022_ = lean_unbox_usize(v_sz_2019_);
lean_dec(v_sz_2019_);
v_i_boxed_2023_ = lean_unbox_usize(v_i_2020_);
lean_dec(v_i_2020_);
v_res_2024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_2022_, v_i_boxed_2023_, v_bs_2021_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object* v_types_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2031_ = lean_array_get_size(v_types_2025_);
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_dec_eq(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
size_t v_sz_2034_; size_t v___x_2035_; lean_object* v___x_2036_; 
v_sz_2034_ = lean_array_size(v_types_2025_);
v___x_2035_ = ((size_t)0ULL);
v___x_2036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2034_, v___x_2035_, v_types_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; lean_object* v___y_2058_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc_n(v_a_2037_, 2);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = lean_box(v___x_2033_);
v___f_2039_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2039_, 0, v_a_2037_);
lean_closure_set(v___f_2039_, 1, v___x_2032_);
lean_closure_set(v___f_2039_, 2, v___x_2038_);
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_array_get_size(v_a_2037_);
v___x_2069_ = lean_nat_dec_lt(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
goto v___jp_2040_;
}
else
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_nat_dec_le(v___x_2068_, v___x_2068_);
if (v___x_2071_ == 0)
{
if (v___x_2069_ == 0)
{
goto v___jp_2040_;
}
else
{
size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_usize_of_nat(v___x_2068_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2037_, v___x_2035_, v___x_2072_, v___x_2070_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
v___y_2058_ = v___x_2073_;
goto v___jp_2057_;
}
}
else
{
size_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_usize_of_nat(v___x_2068_);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2037_, v___x_2035_, v___x_2074_, v___x_2070_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
v___y_2058_ = v___x_2075_;
goto v___jp_2057_;
}
}
v___jp_2040_:
{
size_t v_sz_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_sz_2041_ = lean_array_size(v_a_2037_);
v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_2041_, v___x_2035_, v_a_2037_);
v___x_2043_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2042_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2046_ = l_Lean_Core_mkFreshUserName(v___x_2045_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2047_, v_a_2044_, v___f_2039_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
return v___x_2048_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_a_2044_);
lean_dec_ref(v___f_2039_);
v_a_2049_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2046_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2046_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_dec_ref(v___f_2039_);
return v___x_2043_;
}
}
v___jp_2057_:
{
if (lean_obj_tag(v___y_2058_) == 0)
{
lean_dec_ref_known(v___y_2058_, 1);
goto v___jp_2040_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v___f_2039_);
lean_dec(v_a_2037_);
v_a_2059_ = lean_ctor_get(v___y_2058_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___y_2058_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___y_2058_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___y_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_a_2076_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2036_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2036_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2084_ = l_Lean_instInhabitedExpr;
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = lean_array_get(v___x_2084_, v_types_2025_, v___x_2085_);
lean_dec_ref(v_types_2025_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object* v_types_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
return v_res_2094_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0));
v___x_2097_ = l_Lean_stringToMessageData(v___x_2096_);
return v___x_2097_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2));
v___x_2100_ = l_Lean_stringToMessageData(v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object* v___x_2101_, lean_object* v_as_2102_, size_t v_i_2103_, size_t v_stop_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_a_2112_; uint8_t v___x_2116_; 
v___x_2116_ = lean_usize_dec_eq(v_i_2103_, v_stop_2104_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_array_uget_borrowed(v_as_2102_, v_i_2103_);
lean_inc_ref(v___x_2101_);
lean_inc(v___x_2117_);
v___x_2118_ = l_Lean_Meta_isExprDefEq(v___x_2117_, v___x_2101_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; uint8_t v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2120_ = lean_unbox(v_a_2119_);
lean_dec(v_a_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
lean_inc(v___x_2117_);
v___x_2122_ = l_Lean_MessageData_ofExpr(v___x_2117_);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2121_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
lean_inc_ref(v___x_2101_);
v___x_2126_ = l_Lean_MessageData_ofExpr(v___x_2101_);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2127_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v_a_2112_ = v_a_2129_;
goto v___jp_2111_;
}
else
{
lean_dec_ref(v___x_2101_);
return v___x_2128_;
}
}
else
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_box(0);
v_a_2112_ = v___x_2130_;
goto v___jp_2111_;
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v___x_2101_);
v_a_2131_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2118_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2118_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v___x_2139_; 
lean_dec_ref(v___x_2101_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v_b_2105_);
return v___x_2139_;
}
v___jp_2111_:
{
size_t v___x_2113_; size_t v___x_2114_; 
v___x_2113_ = ((size_t)1ULL);
v___x_2114_ = lean_usize_add(v_i_2103_, v___x_2113_);
v_i_2103_ = v___x_2114_;
v_b_2105_ = v_a_2112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object* v___x_2140_, lean_object* v_as_2141_, lean_object* v_i_2142_, lean_object* v_stop_2143_, lean_object* v_b_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
size_t v_i_boxed_2150_; size_t v_stop_boxed_2151_; lean_object* v_res_2152_; 
v_i_boxed_2150_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_stop_boxed_2151_ = lean_unbox_usize(v_stop_2143_);
lean_dec(v_stop_2143_);
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2140_, v_as_2141_, v_i_boxed_2150_, v_stop_boxed_2151_, v_b_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec_ref(v_as_2141_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t v_sz_2153_, size_t v_i_2154_, lean_object* v_bs_2155_){
_start:
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_usize_dec_lt(v_i_2154_, v_sz_2153_);
if (v___x_2156_ == 0)
{
return v_bs_2155_;
}
else
{
lean_object* v_v_2157_; lean_object* v___x_2158_; lean_object* v_bs_x27_2159_; lean_object* v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; lean_object* v___x_2163_; 
v_v_2157_ = lean_array_uget(v_bs_2155_, v_i_2154_);
v___x_2158_ = lean_unsigned_to_nat(0u);
v_bs_x27_2159_ = lean_array_uset(v_bs_2155_, v_i_2154_, v___x_2158_);
v___x_2160_ = l_Lean_Expr_bindingBody_x21(v_v_2157_);
lean_dec(v_v_2157_);
v___x_2161_ = ((size_t)1ULL);
v___x_2162_ = lean_usize_add(v_i_2154_, v___x_2161_);
v___x_2163_ = lean_array_uset(v_bs_x27_2159_, v_i_2154_, v___x_2160_);
v_i_2154_ = v___x_2162_;
v_bs_2155_ = v___x_2163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object* v_sz_2165_, lean_object* v_i_2166_, lean_object* v_bs_2167_){
_start:
{
size_t v_sz_boxed_2168_; size_t v_i_boxed_2169_; lean_object* v_res_2170_; 
v_sz_boxed_2168_ = lean_unbox_usize(v_sz_2165_);
lean_dec(v_sz_2165_);
v_i_boxed_2169_ = lean_unbox_usize(v_i_2166_);
lean_dec(v_i_2166_);
v_res_2170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_2168_, v_i_boxed_2169_, v_bs_2167_);
return v_res_2170_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object* v_as_2174_, size_t v_i_2175_, size_t v_stop_2176_, lean_object* v_b_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_a_2184_; uint8_t v___x_2188_; 
v___x_2188_ = lean_usize_dec_eq(v_i_2175_, v_stop_2176_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2189_ = lean_array_uget_borrowed(v_as_2174_, v_i_2175_);
v___x_2190_ = l_Lean_Expr_isArrow(v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
lean_inc(v___x_2189_);
v___x_2192_ = l_Lean_MessageData_ofExpr(v___x_2189_);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2193_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v_a_2184_ = v_a_2195_;
goto v___jp_2183_;
}
else
{
return v___x_2194_;
}
}
else
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_box(0);
v_a_2184_ = v___x_2196_;
goto v___jp_2183_;
}
}
else
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_b_2177_);
return v___x_2197_;
}
v___jp_2183_:
{
size_t v___x_2185_; size_t v___x_2186_; 
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_add(v_i_2175_, v___x_2185_);
v_i_2175_ = v___x_2186_;
v_b_2177_ = v_a_2184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object* v_as_2198_, lean_object* v_i_2199_, lean_object* v_stop_2200_, lean_object* v_b_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
size_t v_i_boxed_2207_; size_t v_stop_boxed_2208_; lean_object* v_res_2209_; 
v_i_boxed_2207_ = lean_unbox_usize(v_i_2199_);
lean_dec(v_i_2199_);
v_stop_boxed_2208_ = lean_unbox_usize(v_stop_2200_);
lean_dec(v_stop_2200_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2198_, v_i_boxed_2207_, v_stop_boxed_2208_, v_b_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec_ref(v_as_2198_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object* v_types_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
size_t v_sz_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
v_sz_2216_ = lean_array_size(v_types_2210_);
v___x_2217_ = ((size_t)0ULL);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2216_, v___x_2217_, v_types_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___y_2223_; size_t v___y_2224_; lean_object* v___y_2231_; size_t v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2259_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = l_Lean_instInhabitedExpr;
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2268_ = lean_array_get_size(v_a_2219_);
v___x_2269_ = lean_nat_dec_lt(v___x_2221_, v___x_2268_);
if (v___x_2269_ == 0)
{
goto v___jp_2242_;
}
else
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_nat_dec_le(v___x_2268_, v___x_2268_);
if (v___x_2271_ == 0)
{
if (v___x_2269_ == 0)
{
goto v___jp_2242_;
}
else
{
size_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_usize_of_nat(v___x_2268_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2219_, v___x_2217_, v___x_2272_, v___x_2270_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
v___y_2259_ = v___x_2273_;
goto v___jp_2258_;
}
}
else
{
size_t v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_usize_of_nat(v___x_2268_);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2219_, v___x_2217_, v___x_2274_, v___x_2270_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
v___y_2259_ = v___x_2275_;
goto v___jp_2258_;
}
}
v___jp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_2224_, v___x_2217_, v_a_2219_);
v___x_2226_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2225_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = lean_array_get(v___x_2220_, v___y_2223_, v___x_2221_);
lean_dec_ref(v___y_2223_);
v___x_2229_ = l_Lean_mkArrow(v_a_2227_, v___x_2228_, v_a_2213_, v_a_2214_);
return v___x_2229_;
}
else
{
lean_dec_ref(v___y_2223_);
return v___x_2226_;
}
}
v___jp_2230_:
{
if (lean_obj_tag(v___y_2233_) == 0)
{
lean_dec_ref_known(v___y_2233_, 1);
v___y_2223_ = v___y_2231_;
v___y_2224_ = v___y_2232_;
goto v___jp_2222_;
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref(v___y_2231_);
lean_dec(v_a_2219_);
v_a_2234_ = lean_ctor_get(v___y_2233_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___y_2233_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___y_2233_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___y_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
v___jp_2242_:
{
size_t v_sz_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_sz_2243_ = lean_array_size(v_a_2219_);
lean_inc(v_a_2219_);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2243_, v___x_2217_, v_a_2219_);
v___x_2245_ = lean_array_get_size(v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_sub(v___x_2245_, v___x_2246_);
v___x_2248_ = lean_array_get(v___x_2220_, v___x_2244_, v___x_2247_);
lean_dec(v___x_2247_);
lean_inc_ref(v___x_2244_);
v___x_2249_ = lean_array_pop(v___x_2244_);
v___x_2250_ = lean_array_get_size(v___x_2249_);
v___x_2251_ = lean_nat_dec_lt(v___x_2221_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2248_);
v___y_2223_ = v___x_2244_;
v___y_2224_ = v_sz_2243_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = lean_box(0);
v___x_2253_ = lean_nat_dec_le(v___x_2250_, v___x_2250_);
if (v___x_2253_ == 0)
{
if (v___x_2251_ == 0)
{
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2248_);
v___y_2223_ = v___x_2244_;
v___y_2224_ = v_sz_2243_;
goto v___jp_2222_;
}
else
{
size_t v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_usize_of_nat(v___x_2250_);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2248_, v___x_2249_, v___x_2217_, v___x_2254_, v___x_2252_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
lean_dec_ref(v___x_2249_);
v___y_2231_ = v___x_2244_;
v___y_2232_ = v_sz_2243_;
v___y_2233_ = v___x_2255_;
goto v___jp_2230_;
}
}
else
{
size_t v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_usize_of_nat(v___x_2250_);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2248_, v___x_2249_, v___x_2217_, v___x_2256_, v___x_2252_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
lean_dec_ref(v___x_2249_);
v___y_2231_ = v___x_2244_;
v___y_2232_ = v_sz_2243_;
v___y_2233_ = v___x_2257_;
goto v___jp_2230_;
}
}
}
v___jp_2258_:
{
if (lean_obj_tag(v___y_2259_) == 0)
{
lean_dec_ref_known(v___y_2259_, 1);
goto v___jp_2242_;
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_a_2219_);
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
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
v_a_2276_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2218_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2218_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object* v_types_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
return v_res_2290_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2));
v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object* v___x_2297_, lean_object* v___x_2298_, lean_object* v_arg_2299_, lean_object* v_arg_2300_, lean_object* v___x_2301_, lean_object* v_a_2302_, lean_object* v_tail_2303_, lean_object* v___x_2304_, lean_object* v___x_2305_, lean_object* v___x_2306_, lean_object* v_y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
uint8_t v___x_2349__boxed_2313_; uint8_t v___x_2350__boxed_2314_; uint8_t v___x_2351__boxed_2315_; lean_object* v_res_2316_; 
v___x_2349__boxed_2313_ = lean_unbox(v___x_2304_);
v___x_2350__boxed_2314_ = lean_unbox(v___x_2305_);
v___x_2351__boxed_2315_ = lean_unbox(v___x_2306_);
v_res_2316_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v___x_2297_, v___x_2298_, v_arg_2299_, v_arg_2300_, v___x_2301_, v_a_2302_, v_tail_2303_, v___x_2349__boxed_2313_, v___x_2350__boxed_2314_, v___x_2351__boxed_2315_, v_y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object* v_x_2317_, lean_object* v_codomain_2318_, lean_object* v_alts_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
if (lean_obj_tag(v_alts_2319_) == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref(v_codomain_2318_);
lean_dec_ref(v_x_2317_);
v___x_2325_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
v___x_2326_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2325_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
return v___x_2326_;
}
else
{
lean_object* v_tail_2327_; 
v_tail_2327_ = lean_ctor_get(v_alts_2319_, 1);
if (lean_obj_tag(v_tail_2327_) == 0)
{
lean_object* v_head_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v_codomain_2318_);
v_head_2328_ = lean_ctor_get(v_alts_2319_, 0);
lean_inc(v_head_2328_);
lean_dec_ref_known(v_alts_2319_, 2);
v___x_2329_ = lean_unsigned_to_nat(1u);
v___x_2330_ = lean_mk_empty_array_with_capacity(v___x_2329_);
v___x_2331_ = lean_array_push(v___x_2330_, v_x_2317_);
v___x_2332_ = l_Lean_Expr_beta(v_head_2328_, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
else
{
lean_object* v_head_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2419_; 
lean_inc(v_tail_2327_);
v_head_2334_ = lean_ctor_get(v_alts_2319_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_alts_2319_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v_alts_2319_, 1);
lean_dec(v_unused_2420_);
v___x_2336_ = v_alts_2319_;
v_isShared_2337_ = v_isSharedCheck_2419_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_head_2334_);
lean_dec(v_alts_2319_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2419_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; 
lean_inc(v_a_2323_);
lean_inc_ref(v_a_2322_);
lean_inc(v_a_2321_);
lean_inc_ref(v_a_2320_);
lean_inc_ref(v_x_2317_);
v___x_2338_ = lean_infer_type(v_x_2317_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc_n(v_a_2339_, 2);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2339_, v_a_2321_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2351_ = l_Lean_Expr_cleanupAnnotations(v_a_2341_);
v___x_2352_ = l_Lean_Expr_isApp(v___x_2351_);
if (v___x_2352_ == 0)
{
lean_dec_ref(v___x_2351_);
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec(v_tail_2327_);
lean_dec_ref(v_codomain_2318_);
lean_dec_ref(v_x_2317_);
v___y_2343_ = v_a_2320_;
v___y_2344_ = v_a_2321_;
v___y_2345_ = v_a_2322_;
v___y_2346_ = v_a_2323_;
goto v___jp_2342_;
}
else
{
lean_object* v_arg_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v_arg_2353_ = lean_ctor_get(v___x_2351_, 1);
lean_inc_ref(v_arg_2353_);
v___x_2354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2351_);
v___x_2355_ = l_Lean_Expr_isApp(v___x_2354_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v___x_2354_);
lean_dec_ref(v_arg_2353_);
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec(v_tail_2327_);
lean_dec_ref(v_codomain_2318_);
lean_dec_ref(v_x_2317_);
v___y_2343_ = v_a_2320_;
v___y_2344_ = v_a_2321_;
v___y_2345_ = v_a_2322_;
v___y_2346_ = v_a_2323_;
goto v___jp_2342_;
}
else
{
lean_object* v_arg_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v_arg_2356_ = lean_ctor_get(v___x_2354_, 1);
lean_inc_ref(v_arg_2356_);
v___x_2357_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2354_);
v___x_2358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0));
v___x_2359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_2360_ = l_Lean_Expr_isConstOf(v___x_2357_, v___x_2359_);
lean_dec_ref(v___x_2357_);
if (v___x_2360_ == 0)
{
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec(v_tail_2327_);
lean_dec_ref(v_codomain_2318_);
lean_dec_ref(v_x_2317_);
v___y_2343_ = v_a_2320_;
v___y_2344_ = v_a_2321_;
v___y_2345_ = v_a_2322_;
v___y_2346_ = v_a_2323_;
goto v___jp_2342_;
}
else
{
lean_object* v___x_2361_; 
lean_inc_ref(v_codomain_2318_);
v___x_2361_ = l_Lean_Meta_getLevel(v_codomain_2318_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_mk_empty_array_with_capacity(v___x_2363_);
lean_inc_ref(v_x_2317_);
lean_inc_ref(v___x_2364_);
v___x_2365_ = lean_array_push(v___x_2364_, v_x_2317_);
v___x_2366_ = 0;
v___x_2367_ = 1;
v___x_2368_ = l_Lean_Meta_mkLambdaFVars(v___x_2365_, v_codomain_2318_, v___x_2366_, v___x_2360_, v___x_2366_, v___x_2360_, v___x_2367_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec_ref(v___x_2365_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2410_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2410_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2410_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_alt_u2082_2376_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___f_2389_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; 
v___x_2373_ = l_Lean_Expr_getAppFn(v_a_2339_);
lean_dec(v_a_2339_);
v___x_2374_ = l_Lean_Expr_constLevels_x21(v___x_2373_);
lean_dec_ref(v___x_2373_);
v___x_2386_ = lean_box(v___x_2366_);
v___x_2387_ = lean_box(v___x_2360_);
v___x_2388_ = lean_box(v___x_2367_);
lean_inc(v_tail_2327_);
lean_inc(v_a_2369_);
lean_inc_ref(v_arg_2353_);
lean_inc_ref(v_arg_2356_);
lean_inc(v___x_2374_);
v___f_2389_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2389_, 0, v___x_2358_);
lean_closure_set(v___f_2389_, 1, v___x_2374_);
lean_closure_set(v___f_2389_, 2, v_arg_2356_);
lean_closure_set(v___f_2389_, 3, v_arg_2353_);
lean_closure_set(v___f_2389_, 4, v___x_2364_);
lean_closure_set(v___f_2389_, 5, v_a_2369_);
lean_closure_set(v___f_2389_, 6, v_tail_2327_);
lean_closure_set(v___f_2389_, 7, v___x_2386_);
lean_closure_set(v___f_2389_, 8, v___x_2387_);
lean_closure_set(v___f_2389_, 9, v___x_2388_);
if (lean_obj_tag(v_tail_2327_) == 1)
{
lean_object* v_tail_2408_; 
v_tail_2408_ = lean_ctor_get(v_tail_2327_, 1);
if (lean_obj_tag(v_tail_2408_) == 0)
{
lean_object* v_head_2409_; 
lean_dec_ref(v___f_2389_);
v_head_2409_ = lean_ctor_get(v_tail_2327_, 0);
lean_inc(v_head_2409_);
lean_dec_ref_known(v_tail_2327_, 2);
v_alt_u2082_2376_ = v_head_2409_;
goto v___jp_2375_;
}
else
{
lean_dec_ref_known(v_tail_2327_, 2);
v___y_2391_ = v_a_2320_;
v___y_2392_ = v_a_2321_;
v___y_2393_ = v_a_2322_;
v___y_2394_ = v_a_2323_;
goto v___jp_2390_;
}
}
else
{
lean_dec(v_tail_2327_);
v___y_2391_ = v_a_2320_;
v___y_2392_ = v_a_2321_;
v___y_2393_ = v_a_2322_;
v___y_2394_ = v_a_2323_;
goto v___jp_2390_;
}
v___jp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2377_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2374_);
lean_ctor_set(v___x_2336_, 0, v_a_2362_);
v___x_2379_ = v___x_2336_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2362_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v___x_2374_);
v___x_2379_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2380_ = l_Lean_Expr_const___override(v___x_2377_, v___x_2379_);
v___x_2381_ = l_Lean_mkApp6(v___x_2380_, v_arg_2356_, v_arg_2353_, v_a_2369_, v_x_2317_, v_head_2334_, v_alt_u2082_2376_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2381_);
v___x_2383_ = v___x_2371_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
v___jp_2390_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_2396_ = l_Lean_Core_mkFreshUserName(v___x_2395_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
lean_inc_ref(v_arg_2353_);
v___x_2398_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2397_, v_arg_2353_, v___f_2389_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v_alt_u2082_2376_ = v_a_2399_;
goto v___jp_2375_;
}
else
{
lean_dec(v___x_2374_);
lean_del_object(v___x_2371_);
lean_dec(v_a_2369_);
lean_dec(v_a_2362_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec_ref(v_x_2317_);
return v___x_2398_;
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec_ref(v___f_2389_);
lean_dec(v___x_2374_);
lean_del_object(v___x_2371_);
lean_dec(v_a_2369_);
lean_dec(v_a_2362_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec_ref(v_x_2317_);
v_a_2400_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2396_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2396_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
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
}
}
else
{
lean_dec_ref(v___x_2364_);
lean_dec(v_a_2362_);
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec(v_a_2339_);
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec(v_tail_2327_);
lean_dec_ref(v_x_2317_);
return v___x_2368_;
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec_ref(v_arg_2356_);
lean_dec_ref(v_arg_2353_);
lean_dec(v_a_2339_);
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec(v_tail_2327_);
lean_dec_ref(v_codomain_2318_);
lean_dec_ref(v_x_2317_);
v_a_2411_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2361_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2361_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
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
}
}
v___jp_2342_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
v___x_2348_ = l_Lean_MessageData_ofExpr(v_a_2339_);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2349_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
return v___x_2350_;
}
}
else
{
lean_dec(v_a_2339_);
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec(v_tail_2327_);
lean_dec_ref(v_codomain_2318_);
lean_dec_ref(v_x_2317_);
return v___x_2340_;
}
}
else
{
lean_del_object(v___x_2336_);
lean_dec(v_head_2334_);
lean_dec(v_tail_2327_);
lean_dec_ref(v_codomain_2318_);
lean_dec_ref(v_x_2317_);
return v___x_2338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object* v___x_2421_, lean_object* v___x_2422_, lean_object* v_arg_2423_, lean_object* v_arg_2424_, lean_object* v___x_2425_, lean_object* v_a_2426_, lean_object* v_tail_2427_, uint8_t v___x_2428_, uint8_t v___x_2429_, uint8_t v___x_2430_, lean_object* v_y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2437_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3));
v___x_2438_ = l_Lean_Name_mkStr2(v___x_2421_, v___x_2437_);
v___x_2439_ = l_Lean_Expr_const___override(v___x_2438_, v___x_2422_);
lean_inc_ref_n(v_y_2431_, 2);
v___x_2440_ = l_Lean_mkApp3(v___x_2439_, v_arg_2423_, v_arg_2424_, v_y_2431_);
lean_inc_ref(v___x_2425_);
v___x_2441_ = lean_array_push(v___x_2425_, v___x_2440_);
v___x_2442_ = l_Lean_Expr_beta(v_a_2426_, v___x_2441_);
v___x_2443_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_y_2431_, v___x_2442_, v_tail_2427_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = lean_array_push(v___x_2425_, v_y_2431_);
v___x_2446_ = l_Lean_Meta_mkLambdaFVars(v___x_2445_, v_a_2444_, v___x_2428_, v___x_2429_, v___x_2428_, v___x_2429_, v___x_2430_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
lean_dec_ref(v___x_2445_);
return v___x_2446_;
}
else
{
lean_dec_ref(v_y_2431_);
lean_dec_ref(v___x_2425_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object* v_x_2447_, lean_object* v_codomain_2448_, lean_object* v_alts_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2447_, v_codomain_2448_, v_alts_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
return v_res_2455_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2457_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2458_ = lean_unsigned_to_nat(21u);
v___x_2459_ = lean_unsigned_to_nat(414u);
v___x_2460_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0));
v___x_2461_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2462_ = l_mkPanicMessageWithDecl(v___x_2461_, v___x_2460_, v___x_2459_, v___x_2458_, v___x_2457_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object* v___x_2463_, lean_object* v_es_2464_, lean_object* v_xs_2465_, lean_object* v_codomain_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = lean_array_get_size(v_xs_2465_);
v___x_2473_ = lean_nat_dec_eq(v___x_2472_, v___x_2463_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_dec_ref(v_codomain_2466_);
lean_dec_ref(v_es_2464_);
v___x_2474_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1);
v___x_2475_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2474_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = lean_unsigned_to_nat(0u);
v___x_2477_ = lean_array_fget_borrowed(v_xs_2465_, v___x_2476_);
v___x_2478_ = lean_array_to_list(v_es_2464_);
lean_inc(v___x_2477_);
v___x_2479_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2477_, v_codomain_2466_, v___x_2478_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2481_ = lean_mk_empty_array_with_capacity(v___x_2463_);
lean_inc(v___x_2477_);
v___x_2482_ = lean_array_push(v___x_2481_, v___x_2477_);
v___x_2483_ = 0;
v___x_2484_ = 1;
v___x_2485_ = l_Lean_Meta_mkLambdaFVars(v___x_2482_, v_a_2480_, v___x_2483_, v___x_2473_, v___x_2483_, v___x_2473_, v___x_2484_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec_ref(v___x_2482_);
return v___x_2485_;
}
else
{
return v___x_2479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(lean_object* v___x_2486_, lean_object* v_es_2487_, lean_object* v_xs_2488_, lean_object* v_codomain_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(v___x_2486_, v_es_2487_, v_xs_2488_, v_codomain_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v_xs_2488_);
lean_dec(v___x_2486_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(lean_object* v_resultType_2496_, lean_object* v_es_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2507_; 
v___x_2503_ = lean_unsigned_to_nat(1u);
v___f_2504_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2504_, 0, v___x_2503_);
lean_closure_set(v___f_2504_, 1, v_es_2497_);
v___x_2505_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2506_ = 0;
v___x_2507_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_resultType_2496_, v___x_2505_, v___f_2504_, v___x_2506_, v___x_2506_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(lean_object* v_resultType_2508_, lean_object* v_es_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_2508_, v_es_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(size_t v_sz_2516_, size_t v_i_2517_, lean_object* v_bs_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_usize_dec_lt(v_i_2517_, v_sz_2516_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_bs_2518_);
return v___x_2525_;
}
else
{
lean_object* v_v_2526_; lean_object* v___x_2527_; 
v_v_2526_ = lean_array_uget_borrowed(v_bs_2518_, v_i_2517_);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v_v_2526_);
v___x_2527_ = lean_infer_type(v_v_2526_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v_bs_x27_2530_; size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = lean_unsigned_to_nat(0u);
v_bs_x27_2530_ = lean_array_uset(v_bs_2518_, v_i_2517_, v___x_2529_);
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2517_, v___x_2531_);
v___x_2533_ = lean_array_uset(v_bs_x27_2530_, v_i_2517_, v_a_2528_);
v_i_2517_ = v___x_2532_;
v_bs_2518_ = v___x_2533_;
goto _start;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_bs_2518_);
v_a_2535_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2527_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2527_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(lean_object* v_sz_2543_, lean_object* v_i_2544_, lean_object* v_bs_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
size_t v_sz_boxed_2551_; size_t v_i_boxed_2552_; lean_object* v_res_2553_; 
v_sz_boxed_2551_ = lean_unbox_usize(v_sz_2543_);
lean_dec(v_sz_2543_);
v_i_boxed_2552_ = lean_unbox_usize(v_i_2544_);
lean_dec(v_i_2544_);
v_res_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_boxed_2551_, v_i_boxed_2552_, v_bs_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry(lean_object* v_es_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
size_t v_sz_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v_sz_2560_ = lean_array_size(v_es_2554_);
v___x_2561_ = ((size_t)0ULL);
lean_inc_ref(v_es_2554_);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2560_, v___x_2561_, v_es_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2563_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2566_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v___x_2564_, 1);
v___x_2566_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_a_2565_, v_es_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
return v___x_2566_;
}
else
{
lean_dec_ref(v_es_2554_);
return v___x_2564_;
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec_ref(v_es_2554_);
v_a_2567_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2562_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2562_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(lean_object* v_es_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_es_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
return v_res_2581_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2583_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2584_ = lean_unsigned_to_nat(21u);
v___x_2585_ = lean_unsigned_to_nat(434u);
v___x_2586_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0));
v___x_2587_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2588_ = l_mkPanicMessageWithDecl(v___x_2587_, v___x_2586_, v___x_2585_, v___x_2584_, v___x_2583_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(lean_object* v___x_2589_, lean_object* v_es_2590_, lean_object* v_xs_2591_, lean_object* v_codomain_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_array_get_size(v_xs_2591_);
v___x_2599_ = lean_nat_dec_eq(v___x_2598_, v___x_2589_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v_codomain_2592_);
lean_dec_ref(v_es_2590_);
v___x_2600_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1);
v___x_2601_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2600_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_array_fget_borrowed(v_xs_2591_, v___x_2602_);
v___x_2604_ = lean_array_to_list(v_es_2590_);
lean_inc(v___x_2603_);
v___x_2605_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2603_, v_codomain_2592_, v___x_2604_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = lean_mk_empty_array_with_capacity(v___x_2589_);
lean_inc(v___x_2603_);
v___x_2608_ = lean_array_push(v___x_2607_, v___x_2603_);
v___x_2609_ = 0;
v___x_2610_ = 1;
v___x_2611_ = l_Lean_Meta_mkLambdaFVars(v___x_2608_, v_a_2606_, v___x_2609_, v___x_2599_, v___x_2609_, v___x_2599_, v___x_2610_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec_ref(v___x_2608_);
return v___x_2611_;
}
else
{
return v___x_2605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object* v___x_2612_, lean_object* v_es_2613_, lean_object* v_xs_2614_, lean_object* v_codomain_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2612_, v_es_2613_, v_xs_2614_, v_codomain_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec_ref(v_xs_2614_);
lean_dec(v___x_2612_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object* v_es_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
size_t v_sz_2628_; size_t v___x_2629_; lean_object* v___x_2630_; 
v_sz_2628_ = lean_array_size(v_es_2622_);
v___x_2629_ = ((size_t)0ULL);
lean_inc_ref(v_es_2622_);
v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2628_, v___x_2629_, v_es_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2632_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2632_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_a_2631_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2634_; lean_object* v___f_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; lean_object* v___x_2638_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = lean_unsigned_to_nat(1u);
v___f_2635_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2635_, 0, v___x_2634_);
lean_closure_set(v___f_2635_, 1, v_es_2622_);
v___x_2636_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2637_ = 0;
v___x_2638_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_2633_, v___x_2636_, v___f_2635_, v___x_2637_, v___x_2637_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
return v___x_2638_;
}
else
{
lean_dec_ref(v_es_2622_);
return v___x_2632_;
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref(v_es_2622_);
v_a_2639_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2630_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2630_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object* v_es_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object* v_a_2654_, lean_object* v_domain_2655_, lean_object* v___x_2656_, lean_object* v_type_2657_, uint8_t v___x_2658_, lean_object* v_x_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = l_List_lengthTR___redArg(v_a_2654_);
lean_inc_ref(v_x_2659_);
v___x_2666_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2665_, v_domain_2655_, v___x_2656_, v_x_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___x_2665_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_mk_empty_array_with_capacity(v___x_2668_);
lean_inc_ref(v___x_2669_);
v___x_2670_ = lean_array_push(v___x_2669_, v_a_2667_);
v___x_2671_ = l_Lean_Meta_instantiateForall(v_type_2657_, v___x_2670_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec_ref(v___x_2670_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2673_ = lean_array_push(v___x_2669_, v_x_2659_);
v___x_2674_ = 0;
v___x_2675_ = 1;
v___x_2676_ = l_Lean_Meta_mkForallFVars(v___x_2673_, v_a_2672_, v___x_2674_, v___x_2658_, v___x_2658_, v___x_2675_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec_ref(v___x_2673_);
return v___x_2676_;
}
else
{
lean_dec_ref(v___x_2669_);
lean_dec_ref(v_x_2659_);
return v___x_2671_;
}
}
else
{
lean_dec_ref(v_x_2659_);
lean_dec_ref(v_type_2657_);
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object* v_a_2677_, lean_object* v_domain_2678_, lean_object* v___x_2679_, lean_object* v_type_2680_, lean_object* v___x_2681_, lean_object* v_x_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v___x_788__boxed_2688_; lean_object* v_res_2689_; 
v___x_788__boxed_2688_ = lean_unbox(v___x_2681_);
v_res_2689_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2677_, v_domain_2678_, v___x_2679_, v_type_2680_, v___x_788__boxed_2688_, v_x_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___x_2679_);
lean_dec(v_a_2677_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object* v_a_2690_, lean_object* v_domain_2691_, lean_object* v_type_2692_, size_t v_sz_2693_, size_t v_i_2694_, lean_object* v_bs_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_usize_dec_lt(v_i_2694_, v_sz_2693_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; 
lean_dec_ref(v_type_2692_);
lean_dec_ref(v_domain_2691_);
lean_dec(v_a_2690_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v_bs_2695_);
return v___x_2702_;
}
else
{
lean_object* v_v_2703_; lean_object* v___x_2704_; lean_object* v_bs_x27_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_v_2703_ = lean_array_uget(v_bs_2695_, v_i_2694_);
v___x_2704_ = lean_unsigned_to_nat(0u);
v_bs_x27_2705_ = lean_array_uset(v_bs_2695_, v_i_2694_, v___x_2704_);
v___x_2706_ = lean_usize_to_nat(v_i_2694_);
v___x_2707_ = lean_box(v___x_2701_);
lean_inc_ref(v_type_2692_);
lean_inc_ref(v_domain_2691_);
lean_inc(v_a_2690_);
v___f_2708_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2708_, 0, v_a_2690_);
lean_closure_set(v___f_2708_, 1, v_domain_2691_);
lean_closure_set(v___f_2708_, 2, v___x_2706_);
lean_closure_set(v___f_2708_, 3, v_type_2692_);
lean_closure_set(v___f_2708_, 4, v___x_2707_);
v___x_2709_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2710_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_2709_, v_v_2703_, v___f_2708_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; size_t v___x_2712_; size_t v___x_2713_; lean_object* v___x_2714_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = ((size_t)1ULL);
v___x_2713_ = lean_usize_add(v_i_2694_, v___x_2712_);
v___x_2714_ = lean_array_uset(v_bs_x27_2705_, v_i_2694_, v_a_2711_);
v_i_2694_ = v___x_2713_;
v_bs_2695_ = v___x_2714_;
goto _start;
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec_ref(v_bs_x27_2705_);
lean_dec_ref(v_type_2692_);
lean_dec_ref(v_domain_2691_);
lean_dec(v_a_2690_);
v_a_2716_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2710_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2710_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object* v_a_2724_, lean_object* v_domain_2725_, lean_object* v_type_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_bs_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
size_t v_sz_boxed_2735_; size_t v_i_boxed_2736_; lean_object* v_res_2737_; 
v_sz_boxed_2735_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2736_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2724_, v_domain_2725_, v_type_2726_, v_sz_boxed_2735_, v_i_boxed_2736_, v_bs_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object* v_n_2738_, lean_object* v_type_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; uint8_t v___x_2765_; 
v___x_2765_ = l_Lean_Expr_isForall(v_type_2739_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
v___x_2766_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_2767_ = l_Lean_MessageData_ofExpr(v_type_2739_);
v___x_2768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2768_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
else
{
v___y_2746_ = v_a_2740_;
v___y_2747_ = v_a_2741_;
v___y_2748_ = v_a_2742_;
v___y_2749_ = v_a_2743_;
goto v___jp_2745_;
}
v___jp_2745_:
{
lean_object* v_domain_2750_; lean_object* v___x_2751_; 
v_domain_2750_ = l_Lean_Expr_bindingDomain_x21(v_type_2739_);
lean_inc_ref(v_domain_2750_);
v___x_2751_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_2738_, v_domain_2750_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2753_; size_t v_sz_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc_n(v_a_2752_, 2);
lean_dec_ref_known(v___x_2751_, 1);
v___x_2753_ = lean_array_mk(v_a_2752_);
v_sz_2754_ = lean_array_size(v___x_2753_);
v___x_2755_ = ((size_t)0ULL);
v___x_2756_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2752_, v_domain_2750_, v_type_2739_, v_sz_2754_, v___x_2755_, v___x_2753_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2756_;
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref(v_domain_2750_);
lean_dec_ref(v_type_2739_);
v_a_2757_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2751_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2751_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object* v_n_2778_, lean_object* v_type_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2778_, v_type_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_n_2778_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object* v_a_2786_, lean_object* v_domain_2787_, lean_object* v_type_2788_, lean_object* v_as_2789_, size_t v_sz_2790_, size_t v_i_2791_, lean_object* v_bs_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2786_, v_domain_2787_, v_type_2788_, v_sz_2790_, v_i_2791_, v_bs_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object* v_a_2799_, lean_object* v_domain_2800_, lean_object* v_type_2801_, lean_object* v_as_2802_, lean_object* v_sz_2803_, lean_object* v_i_2804_, lean_object* v_bs_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
size_t v_sz_boxed_2811_; size_t v_i_boxed_2812_; lean_object* v_res_2813_; 
v_sz_boxed_2811_ = lean_unbox_usize(v_sz_2803_);
lean_dec(v_sz_2803_);
v_i_boxed_2812_ = lean_unbox_usize(v_i_2804_);
lean_dec(v_i_2804_);
v_res_2813_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2799_, v_domain_2800_, v_type_2801_, v_as_2802_, v_sz_boxed_2811_, v_i_boxed_2812_, v_bs_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v_as_2802_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object* v_argsPacker_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_array_get_size(v_argsPacker_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object* v_argsPacker_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_2816_);
lean_dec_ref(v_argsPacker_2816_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t v_sz_2818_, size_t v_i_2819_, lean_object* v_bs_2820_){
_start:
{
uint8_t v___x_2821_; 
v___x_2821_ = lean_usize_dec_lt(v_i_2819_, v_sz_2818_);
if (v___x_2821_ == 0)
{
return v_bs_2820_;
}
else
{
lean_object* v_v_2822_; lean_object* v___x_2823_; lean_object* v_bs_x27_2824_; lean_object* v___x_2825_; size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v_v_2822_ = lean_array_uget(v_bs_2820_, v_i_2819_);
v___x_2823_ = lean_unsigned_to_nat(0u);
v_bs_x27_2824_ = lean_array_uset(v_bs_2820_, v_i_2819_, v___x_2823_);
v___x_2825_ = lean_array_get_size(v_v_2822_);
lean_dec(v_v_2822_);
v___x_2826_ = ((size_t)1ULL);
v___x_2827_ = lean_usize_add(v_i_2819_, v___x_2826_);
v___x_2828_ = lean_array_uset(v_bs_x27_2824_, v_i_2819_, v___x_2825_);
v_i_2819_ = v___x_2827_;
v_bs_2820_ = v___x_2828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object* v_sz_2830_, lean_object* v_i_2831_, lean_object* v_bs_2832_){
_start:
{
size_t v_sz_boxed_2833_; size_t v_i_boxed_2834_; lean_object* v_res_2835_; 
v_sz_boxed_2833_ = lean_unbox_usize(v_sz_2830_);
lean_dec(v_sz_2830_);
v_i_boxed_2834_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_res_2835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_2833_, v_i_boxed_2834_, v_bs_2832_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object* v_argsPacker_2836_){
_start:
{
size_t v_sz_2837_; size_t v___x_2838_; lean_object* v___x_2839_; 
v_sz_2837_ = lean_array_size(v_argsPacker_2836_);
v___x_2838_ = ((size_t)0ULL);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2837_, v___x_2838_, v_argsPacker_2836_);
return v___x_2839_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0(void){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Array_instInhabited(lean_box(0));
return v___x_2840_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object* v_argsPacker_2841_){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2842_ = lean_array_get_size(v_argsPacker_2841_);
v___x_2843_ = lean_unsigned_to_nat(1u);
v___x_2844_ = lean_nat_dec_eq(v___x_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
return v___x_2844_;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2845_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2846_ = lean_unsigned_to_nat(0u);
v___x_2847_ = lean_array_get_borrowed(v___x_2845_, v_argsPacker_2841_, v___x_2846_);
v___x_2848_ = lean_array_get_size(v___x_2847_);
v___x_2849_ = lean_nat_dec_eq(v___x_2848_, v___x_2843_);
return v___x_2849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object* v_argsPacker_2850_){
_start:
{
uint8_t v_res_2851_; lean_object* v_r_2852_; 
v_res_2851_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2850_);
lean_dec_ref(v_argsPacker_2850_);
v_r_2852_ = lean_box(v_res_2851_);
return v_r_2852_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__2(void){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2855_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__1));
v___x_2856_ = lean_unsigned_to_nat(2u);
v___x_2857_ = lean_unsigned_to_nat(469u);
v___x_2858_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2859_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2860_ = l_mkPanicMessageWithDecl(v___x_2859_, v___x_2858_, v___x_2857_, v___x_2856_, v___x_2855_);
return v___x_2860_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__4(void){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2862_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__3));
v___x_2863_ = lean_unsigned_to_nat(2u);
v___x_2864_ = lean_unsigned_to_nat(470u);
v___x_2865_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2866_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2867_ = l_mkPanicMessageWithDecl(v___x_2866_, v___x_2865_, v___x_2864_, v___x_2863_, v___x_2862_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object* v_argsPacker_2868_, lean_object* v_domain_2869_, lean_object* v_fidx_2870_, lean_object* v_args_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = lean_array_get_size(v_argsPacker_2868_);
v___x_2878_ = lean_nat_dec_lt(v_fidx_2870_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_dec(v_fidx_2870_);
lean_dec_ref(v_domain_2869_);
v___x_2879_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__2, &l_Lean_Meta_ArgsPacker_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__2);
v___x_2880_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2879_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
return v___x_2880_;
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2881_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2882_ = lean_array_get_size(v_args_2871_);
v___x_2883_ = lean_array_get_borrowed(v___x_2881_, v_argsPacker_2868_, v_fidx_2870_);
v___x_2884_ = lean_array_get_size(v___x_2883_);
v___x_2885_ = lean_nat_dec_eq(v___x_2882_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_dec(v_fidx_2870_);
lean_dec_ref(v_domain_2869_);
v___x_2886_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__4, &l_Lean_Meta_ArgsPacker_pack___closed__4_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__4);
v___x_2887_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2886_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
return v___x_2887_;
}
else
{
lean_object* v___x_2888_; 
lean_inc_ref(v_domain_2869_);
v___x_2888_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_2877_, v_domain_2869_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
v___x_2890_ = l_Lean_instInhabitedExpr;
lean_inc(v_fidx_2870_);
v___x_2891_ = l_List_get_x21Internal___redArg(v___x_2890_, v_a_2889_, v_fidx_2870_);
lean_dec(v_a_2889_);
v___x_2892_ = l_Lean_Meta_ArgsPacker_Unary_pack(v___x_2891_, v_args_2871_);
lean_dec(v___x_2891_);
v___x_2893_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2877_, v_domain_2869_, v_fidx_2870_, v___x_2892_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
lean_dec(v_fidx_2870_);
return v___x_2893_;
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_fidx_2870_);
lean_dec_ref(v_domain_2869_);
v_a_2894_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2888_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2888_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object* v_argsPacker_2902_, lean_object* v_domain_2903_, lean_object* v_fidx_2904_, lean_object* v_args_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2902_, v_domain_2903_, v_fidx_2904_, v_args_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_args_2905_);
lean_dec_ref(v_argsPacker_2902_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object* v_argsPacker_2912_, lean_object* v_e_2913_){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_array_get_size(v_argsPacker_2912_);
v___x_2915_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_2914_, v_e_2913_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_box(0);
return v___x_2916_;
}
else
{
lean_object* v_val_2917_; lean_object* v_fst_2918_; lean_object* v_snd_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2939_; 
v_val_2917_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_val_2917_);
lean_dec_ref_known(v___x_2915_, 1);
v_fst_2918_ = lean_ctor_get(v_val_2917_, 0);
v_snd_2919_ = lean_ctor_get(v_val_2917_, 1);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_val_2917_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2921_ = v_val_2917_;
v_isShared_2922_ = v_isSharedCheck_2939_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_snd_2919_);
lean_inc(v_fst_2918_);
lean_dec(v_val_2917_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2939_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2923_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2924_ = lean_array_get_borrowed(v___x_2923_, v_argsPacker_2912_, v_fst_2918_);
v___x_2925_ = lean_array_get_size(v___x_2924_);
v___x_2926_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_2925_, v_snd_2919_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v___x_2927_; 
lean_del_object(v___x_2921_);
lean_dec(v_fst_2918_);
v___x_2927_ = lean_box(0);
return v___x_2927_;
}
else
{
lean_object* v_val_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2938_; 
v_val_2928_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2930_ = v___x_2926_;
v_isShared_2931_ = v_isSharedCheck_2938_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_val_2928_);
lean_dec(v___x_2926_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2938_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v_val_2928_);
v___x_2933_ = v___x_2921_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_fst_2918_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_val_2928_);
v___x_2933_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2935_; 
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2933_);
v___x_2935_ = v___x_2930_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2933_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object* v_argsPacker_2940_, lean_object* v_e_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_2940_, v_e_2941_);
lean_dec_ref(v_argsPacker_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object* v_as_2943_, lean_object* v_bs_2944_, lean_object* v_i_2945_, lean_object* v_cs_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; uint8_t v___x_2953_; 
v___x_2952_ = lean_array_get_size(v_as_2943_);
v___x_2953_ = lean_nat_dec_lt(v_i_2945_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; 
lean_dec(v_i_2945_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_cs_2946_);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2955_ = lean_array_get_size(v_bs_2944_);
v___x_2956_ = lean_nat_dec_lt(v_i_2945_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
lean_dec(v_i_2945_);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_cs_2946_);
return v___x_2957_;
}
else
{
lean_object* v_a_2958_; lean_object* v_b_2959_; lean_object* v___x_2960_; 
v_a_2958_ = lean_array_fget_borrowed(v_as_2943_, v_i_2945_);
v_b_2959_ = lean_array_fget_borrowed(v_bs_2944_, v_i_2945_);
lean_inc(v_b_2959_);
lean_inc(v_a_2958_);
v___x_2960_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_a_2958_, v_b_2959_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_add(v_i_2945_, v___x_2962_);
lean_dec(v_i_2945_);
v___x_2964_ = lean_array_push(v_cs_2946_, v_a_2961_);
v_i_2945_ = v___x_2963_;
v_cs_2946_ = v___x_2964_;
goto _start;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v_cs_2946_);
lean_dec(v_i_2945_);
v_a_2966_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2960_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2960_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object* v_as_2974_, lean_object* v_bs_2975_, lean_object* v_i_2976_, lean_object* v_cs_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_2974_, v_bs_2975_, v_i_2976_, v_cs_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v_bs_2975_);
lean_dec_ref(v_as_2974_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object* v_argsPacker_2984_, lean_object* v_types_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2991_ = lean_unsigned_to_nat(0u);
v___x_2992_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_2993_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_argsPacker_2984_, v_types_2985_, v___x_2991_, v___x_2992_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2994_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
return v___x_2995_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
v_a_2996_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2993_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2993_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object* v_argsPacker_3004_, lean_object* v_types_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_3004_, v_types_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec_ref(v_types_3005_);
lean_dec_ref(v_argsPacker_3004_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object* v_as_3012_, lean_object* v_bs_3013_, lean_object* v_i_3014_, lean_object* v_cs_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; uint8_t v___x_3022_; 
v___x_3021_ = lean_array_get_size(v_as_3012_);
v___x_3022_ = lean_nat_dec_lt(v_i_3014_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; 
lean_dec(v_i_3014_);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_cs_3015_);
return v___x_3023_;
}
else
{
lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3024_ = lean_array_get_size(v_bs_3013_);
v___x_3025_ = lean_nat_dec_lt(v_i_3014_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
lean_dec(v_i_3014_);
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v_cs_3015_);
return v___x_3026_;
}
else
{
lean_object* v_a_3027_; lean_object* v_b_3028_; lean_object* v___x_3029_; 
v_a_3027_ = lean_array_fget_borrowed(v_as_3012_, v_i_3014_);
v_b_3028_ = lean_array_fget_borrowed(v_bs_3013_, v_i_3014_);
lean_inc(v_b_3028_);
lean_inc(v_a_3027_);
v___x_3029_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_a_3027_, v_b_3028_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = lean_unsigned_to_nat(1u);
v___x_3032_ = lean_nat_add(v_i_3014_, v___x_3031_);
lean_dec(v_i_3014_);
v___x_3033_ = lean_array_push(v_cs_3015_, v_a_3030_);
v_i_3014_ = v___x_3032_;
v_cs_3015_ = v___x_3033_;
goto _start;
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec_ref(v_cs_3015_);
lean_dec(v_i_3014_);
v_a_3035_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3029_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3029_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object* v_as_3043_, lean_object* v_bs_3044_, lean_object* v_i_3045_, lean_object* v_cs_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3043_, v_bs_3044_, v_i_3045_, v_cs_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec_ref(v_bs_3044_);
lean_dec_ref(v_as_3043_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object* v_argsPacker_3053_, lean_object* v_es_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_unsigned_to_nat(0u);
v___x_3061_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3062_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3053_, v_es_3054_, v___x_3060_, v___x_3061_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___x_3064_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_a_3063_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
return v___x_3064_;
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
v_a_3065_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3062_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3062_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object* v_argsPacker_3073_, lean_object* v_es_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3073_, v_es_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec_ref(v_es_3074_);
lean_dec_ref(v_argsPacker_3073_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object* v_argsPacker_3081_, lean_object* v_resultType_3082_, lean_object* v_es_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = lean_unsigned_to_nat(0u);
v___x_3090_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3091_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3081_, v_es_3083_, v___x_3089_, v___x_3090_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3093_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref_known(v___x_3091_, 1);
v___x_3093_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_3082_, v_a_3092_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
return v___x_3093_;
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v_resultType_3082_);
v_a_3094_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3091_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3091_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object* v_argsPacker_3102_, lean_object* v_resultType_3103_, lean_object* v_es_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3102_, v_resultType_3103_, v_es_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_);
lean_dec(v_a_3108_);
lean_dec_ref(v_a_3107_);
lean_dec(v_a_3106_);
lean_dec_ref(v_a_3105_);
lean_dec_ref(v_es_3104_);
lean_dec_ref(v_argsPacker_3102_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object* v_argsPacker_3111_, lean_object* v_es_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_unsigned_to_nat(0u);
v___x_3119_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3120_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3111_, v_es_3112_, v___x_3118_, v___x_3119_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3122_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_a_3121_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
return v___x_3122_;
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
v_a_3123_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3120_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3120_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object* v_argsPacker_3131_, lean_object* v_es_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3131_, v_es_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec_ref(v_es_3132_);
lean_dec_ref(v_argsPacker_3131_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object* v_msg_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___f_3145_; lean_object* v___x_920__overap_3146_; lean_object* v___x_3147_; 
v___f_3145_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_920__overap_3146_ = lean_panic_fn_borrowed(v___f_3145_, v_msg_3139_);
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
lean_inc(v___y_3141_);
lean_inc_ref(v___y_3140_);
v___x_3147_ = lean_apply_5(v___x_920__overap_3146_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, lean_box(0));
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object* v_msg_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object* v_a_3155_, lean_object* v___x_3156_, lean_object* v_i_3157_, lean_object* v_e_3158_, lean_object* v_x_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = l_List_lengthTR___redArg(v_a_3155_);
lean_inc_ref(v_x_3159_);
v___x_3166_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_3165_, v___x_3156_, v_i_3157_, v_x_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___x_3165_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; uint8_t v___x_3174_; uint8_t v___x_3175_; lean_object* v___x_3176_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3166_, 1);
v___x_3168_ = lean_unsigned_to_nat(1u);
v___x_3169_ = lean_mk_empty_array_with_capacity(v___x_3168_);
lean_inc_ref(v___x_3169_);
v___x_3170_ = lean_array_push(v___x_3169_, v_x_3159_);
v___x_3171_ = lean_array_push(v___x_3169_, v_a_3167_);
v___x_3172_ = l_Lean_Expr_beta(v_e_3158_, v___x_3171_);
v___x_3173_ = 0;
v___x_3174_ = 1;
v___x_3175_ = 1;
v___x_3176_ = l_Lean_Meta_mkLambdaFVars(v___x_3170_, v___x_3172_, v___x_3173_, v___x_3174_, v___x_3173_, v___x_3174_, v___x_3175_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec_ref(v___x_3170_);
return v___x_3176_;
}
else
{
lean_dec_ref(v_x_3159_);
lean_dec_ref(v_e_3158_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object* v_a_3177_, lean_object* v___x_3178_, lean_object* v_i_3179_, lean_object* v_e_3180_, lean_object* v_x_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3177_, v___x_3178_, v_i_3179_, v_e_3180_, v_x_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v_i_3179_);
lean_dec(v_a_3177_);
return v_res_3187_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__0));
v___x_3190_ = l_Lean_stringToMessageData(v___x_3189_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3193_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__3));
v___x_3194_ = lean_unsigned_to_nat(4u);
v___x_3195_ = lean_unsigned_to_nat(535u);
v___x_3196_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__2));
v___x_3197_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_3198_ = l_mkPanicMessageWithDecl(v___x_3197_, v___x_3196_, v___x_3195_, v___x_3194_, v___x_3193_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object* v_argsPacker_3199_, lean_object* v_e_3200_, lean_object* v_i_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v___x_3207_; 
lean_inc(v_a_3205_);
lean_inc_ref(v_a_3204_);
lean_inc(v_a_3203_);
lean_inc_ref(v_a_3202_);
lean_inc_ref(v_e_3200_);
v___x_3207_ = lean_infer_type(v_e_3200_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3209_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
lean_inc(v_a_3205_);
lean_inc_ref(v_a_3204_);
lean_inc(v_a_3203_);
lean_inc_ref(v_a_3202_);
v___x_3209_ = lean_whnf(v_a_3208_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v_n_3226_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; uint8_t v___x_3256_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = l_Lean_instInhabitedExpr;
v___x_3212_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v_n_3226_ = lean_array_get_size(v_argsPacker_3199_);
v___x_3256_ = l_Lean_Expr_isForall(v_a_3210_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__4, &l_Lean_Meta_ArgsPacker_curryProj___closed__4_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4);
v___x_3258_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v___x_3257_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_dec_ref_known(v___x_3258_, 1);
v___y_3228_ = v_a_3202_;
v___y_3229_ = v_a_3203_;
v___y_3230_ = v_a_3204_;
v___y_3231_ = v_a_3205_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_a_3210_);
lean_dec(v_i_3201_);
lean_dec_ref(v_e_3200_);
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
v___y_3228_ = v_a_3202_;
v___y_3229_ = v_a_3203_;
v___y_3230_ = v_a_3204_;
v___y_3231_ = v_a_3205_;
goto v___jp_3227_;
}
v___jp_3213_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_inc(v_i_3201_);
v___x_3220_ = l_List_get_x21Internal___redArg(v___x_3211_, v___y_3214_, v_i_3201_);
lean_dec(v___y_3214_);
v___x_3221_ = l_Lean_Expr_bindingName_x21(v_a_3210_);
lean_dec(v_a_3210_);
v___x_3222_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3221_, v___x_3220_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3222_, 1);
v___x_3224_ = lean_array_get_borrowed(v___x_3212_, v_argsPacker_3199_, v_i_3201_);
lean_dec(v_i_3201_);
lean_inc(v___x_3224_);
v___x_3225_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v___x_3224_, v_a_3223_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3225_;
}
else
{
lean_dec(v_i_3201_);
return v___x_3222_;
}
}
v___jp_3227_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3232_ = l_Lean_Expr_bindingDomain_x21(v_a_3210_);
lean_inc_ref(v___x_3232_);
v___x_3233_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_3226_, v___x_3232_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___f_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc_n(v_a_3234_, 2);
lean_dec_ref_known(v___x_3233_, 1);
lean_inc(v_i_3201_);
v___f_3235_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3235_, 0, v_a_3234_);
lean_closure_set(v___f_3235_, 1, v___x_3232_);
lean_closure_set(v___f_3235_, 2, v_i_3201_);
lean_closure_set(v___f_3235_, 3, v_e_3200_);
v___x_3236_ = l_List_lengthTR___redArg(v_a_3234_);
v___x_3237_ = lean_nat_dec_lt(v_i_3201_, v___x_3236_);
lean_dec(v___x_3236_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v___f_3235_);
lean_dec(v_a_3234_);
lean_dec(v_a_3210_);
lean_dec(v_i_3201_);
v___x_3238_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__1, &l_Lean_Meta_ArgsPacker_curryProj___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1);
v___x_3239_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3238_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
else
{
v___y_3214_ = v_a_3234_;
v___y_3215_ = v___f_3235_;
v___y_3216_ = v___y_3228_;
v___y_3217_ = v___y_3229_;
v___y_3218_ = v___y_3230_;
v___y_3219_ = v___y_3231_;
goto v___jp_3213_;
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v___x_3232_);
lean_dec(v_a_3210_);
lean_dec(v_i_3201_);
lean_dec_ref(v_e_3200_);
v_a_3248_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3233_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3233_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
else
{
lean_dec(v_i_3201_);
lean_dec_ref(v_e_3200_);
return v___x_3209_;
}
}
else
{
lean_dec(v_i_3201_);
lean_dec_ref(v_e_3200_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object* v_argsPacker_3267_, lean_object* v_e_3268_, lean_object* v_i_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3267_, v_e_3268_, v_i_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec_ref(v_argsPacker_3267_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object* v_as_3276_, lean_object* v_bs_3277_, lean_object* v_i_3278_, lean_object* v_cs_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = lean_array_get_size(v_as_3276_);
v___x_3286_ = lean_nat_dec_lt(v_i_3278_, v___x_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; 
lean_dec(v_i_3278_);
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v_cs_3279_);
return v___x_3287_;
}
else
{
lean_object* v___x_3288_; uint8_t v___x_3289_; 
v___x_3288_ = lean_array_get_size(v_bs_3277_);
v___x_3289_ = lean_nat_dec_lt(v_i_3278_, v___x_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; 
lean_dec(v_i_3278_);
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v_cs_3279_);
return v___x_3290_;
}
else
{
lean_object* v_a_3291_; lean_object* v_b_3292_; lean_object* v___x_3293_; 
v_a_3291_ = lean_array_fget_borrowed(v_as_3276_, v_i_3278_);
v_b_3292_ = lean_array_fget_borrowed(v_bs_3277_, v_i_3278_);
lean_inc(v_b_3292_);
lean_inc(v_a_3291_);
v___x_3293_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_3291_, v_b_3292_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
v___x_3295_ = lean_unsigned_to_nat(1u);
v___x_3296_ = lean_nat_add(v_i_3278_, v___x_3295_);
lean_dec(v_i_3278_);
v___x_3297_ = lean_array_push(v_cs_3279_, v_a_3294_);
v_i_3278_ = v___x_3296_;
v_cs_3279_ = v___x_3297_;
goto _start;
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec_ref(v_cs_3279_);
lean_dec(v_i_3278_);
v_a_3299_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3293_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3293_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object* v_as_3307_, lean_object* v_bs_3308_, lean_object* v_i_3309_, lean_object* v_cs_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3307_, v_bs_3308_, v_i_3309_, v_cs_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec_ref(v_bs_3308_);
lean_dec_ref(v_as_3307_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object* v_argsPacker_3317_, lean_object* v_t_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_array_get_size(v_argsPacker_3317_);
v___x_3325_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v___x_3324_, v_t_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = lean_unsigned_to_nat(0u);
v___x_3328_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3329_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_argsPacker_3317_, v_a_3326_, v___x_3327_, v___x_3328_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
lean_dec(v_a_3326_);
return v___x_3329_;
}
else
{
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object* v_argsPacker_3330_, lean_object* v_t_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3330_, v_t_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec_ref(v_argsPacker_3330_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object* v_upperBound_3338_, lean_object* v_argsPacker_3339_, lean_object* v_e_3340_, lean_object* v_a_3341_, lean_object* v_b_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
uint8_t v___x_3348_; 
v___x_3348_ = lean_nat_dec_lt(v_a_3341_, v_upperBound_3338_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
lean_dec(v_a_3341_);
lean_dec_ref(v_e_3340_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_b_3342_);
return v___x_3349_;
}
else
{
lean_object* v___x_3350_; 
lean_inc(v_a_3341_);
lean_inc_ref(v_e_3340_);
v___x_3350_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3339_, v_e_3340_, v_a_3341_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v___x_3352_ = lean_array_push(v_b_3342_, v_a_3351_);
v___x_3353_ = lean_unsigned_to_nat(1u);
v___x_3354_ = lean_nat_add(v_a_3341_, v___x_3353_);
lean_dec(v_a_3341_);
v_a_3341_ = v___x_3354_;
v_b_3342_ = v___x_3352_;
goto _start;
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec_ref(v_b_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_e_3340_);
v_a_3356_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3350_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3350_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object* v_upperBound_3364_, lean_object* v_argsPacker_3365_, lean_object* v_e_3366_, lean_object* v_a_3367_, lean_object* v_b_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3364_, v_argsPacker_3365_, v_e_3366_, v_a_3367_, v_b_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec_ref(v_argsPacker_3365_);
lean_dec(v_upperBound_3364_);
return v_res_3374_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curry___closed__0(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = lean_unsigned_to_nat(0u);
v___x_3376_ = l_Lean_Level_ofNat(v___x_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object* v_argsPacker_3377_, lean_object* v_e_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v_es_3386_; lean_object* v___x_3387_; 
v___x_3384_ = lean_array_get_size(v_argsPacker_3377_);
v___x_3385_ = lean_unsigned_to_nat(0u);
v_es_3386_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3387_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_3384_, v_argsPacker_3377_, v_e_3378_, v___x_3385_, v_es_3386_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v___x_3389_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curry___closed__0, &l_Lean_Meta_ArgsPacker_curry___closed__0_once, _init_l_Lean_Meta_ArgsPacker_curry___closed__0);
v___x_3390_ = l_Lean_Meta_PProdN_mk(v___x_3389_, v_a_3388_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
return v___x_3390_;
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_a_3391_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3387_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3387_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object* v_argsPacker_3399_, lean_object* v_e_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3399_, v_e_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec_ref(v_argsPacker_3399_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object* v_upperBound_3407_, lean_object* v_argsPacker_3408_, lean_object* v_e_3409_, lean_object* v_inst_3410_, lean_object* v_R_3411_, lean_object* v_a_3412_, lean_object* v_b_3413_, lean_object* v_c_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3407_, v_argsPacker_3408_, v_e_3409_, v_a_3412_, v_b_3413_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object* v_upperBound_3421_, lean_object* v_argsPacker_3422_, lean_object* v_e_3423_, lean_object* v_inst_3424_, lean_object* v_R_3425_, lean_object* v_a_3426_, lean_object* v_b_3427_, lean_object* v_c_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3421_, v_argsPacker_3422_, v_e_3423_, v_inst_3424_, v_R_3425_, v_a_3426_, v_b_3427_, v_c_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec_ref(v_argsPacker_3422_);
lean_dec(v_upperBound_3421_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object* v_a_3435_, lean_object* v_argsPacker_3436_, lean_object* v_name_3437_, lean_object* v_k_3438_, lean_object* v_tail_3439_, lean_object* v_x_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3435_, v_argsPacker_3436_, v_name_3437_, v_k_3438_, v_tail_3439_, v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object* v_argsPacker_3447_, lean_object* v_name_3448_, lean_object* v_k_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
if (lean_obj_tag(v_a_3450_) == 0)
{
lean_object* v___x_3457_; 
lean_dec(v_name_3448_);
lean_dec_ref(v_argsPacker_3447_);
lean_inc(v_a_3455_);
lean_inc_ref(v_a_3454_);
lean_inc(v_a_3453_);
lean_inc_ref(v_a_3452_);
v___x_3457_ = lean_apply_6(v_k_3449_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, lean_box(0));
return v___x_3457_;
}
else
{
lean_object* v_head_3458_; lean_object* v_tail_3459_; lean_object* v___f_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v_head_3458_ = lean_ctor_get(v_a_3450_, 0);
lean_inc(v_head_3458_);
v_tail_3459_ = lean_ctor_get(v_a_3450_, 1);
lean_inc(v_tail_3459_);
lean_dec_ref_known(v_a_3450_, 2);
lean_inc(v_name_3448_);
lean_inc_ref(v_argsPacker_3447_);
lean_inc_ref(v_a_3451_);
v___f_3460_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3460_, 0, v_a_3451_);
lean_closure_set(v___f_3460_, 1, v_argsPacker_3447_);
lean_closure_set(v___f_3460_, 2, v_name_3448_);
lean_closure_set(v___f_3460_, 3, v_k_3449_);
lean_closure_set(v___f_3460_, 4, v_tail_3459_);
v___x_3461_ = lean_array_get_size(v_argsPacker_3447_);
lean_dec_ref(v_argsPacker_3447_);
v___x_3462_ = lean_unsigned_to_nat(1u);
v___x_3463_ = lean_nat_dec_eq(v___x_3461_, v___x_3462_);
if (v___x_3463_ == 0)
{
uint8_t v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3464_ = 1;
v___x_3465_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3448_, v___x_3464_);
v___x_3466_ = lean_array_get_size(v_a_3451_);
lean_dec_ref(v_a_3451_);
v___x_3467_ = lean_nat_add(v___x_3466_, v___x_3462_);
v___x_3468_ = l_Nat_reprFast(v___x_3467_);
v___x_3469_ = lean_string_append(v___x_3465_, v___x_3468_);
lean_dec_ref(v___x_3468_);
v___x_3470_ = lean_box(0);
v___x_3471_ = l_Lean_Name_str___override(v___x_3470_, v___x_3469_);
v___x_3472_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3471_, v_head_3458_, v___f_3460_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
return v___x_3472_;
}
else
{
lean_object* v___x_3473_; 
lean_dec_ref(v_a_3451_);
v___x_3473_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_3448_, v_head_3458_, v___f_3460_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
return v___x_3473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object* v_a_3474_, lean_object* v_argsPacker_3475_, lean_object* v_name_3476_, lean_object* v_k_3477_, lean_object* v_tail_3478_, lean_object* v_x_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_array_push(v_a_3474_, v_x_3479_);
v___x_3486_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3475_, v_name_3476_, v_k_3477_, v_tail_3478_, v___x_3485_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object* v_argsPacker_3487_, lean_object* v_name_3488_, lean_object* v_k_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3487_, v_name_3488_, v_k_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object* v_00_u03b1_3498_, lean_object* v_argsPacker_3499_, lean_object* v_name_3500_, lean_object* v_k_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3499_, v_name_3500_, v_k_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object* v_00_u03b1_3510_, lean_object* v_argsPacker_3511_, lean_object* v_name_3512_, lean_object* v_k_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(v_00_u03b1_3510_, v_argsPacker_3511_, v_name_3512_, v_k_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object* v_argsPacker_3522_, lean_object* v_name_3523_, lean_object* v_type_3524_, lean_object* v_k_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3522_, v_type_3524_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = lean_array_to_list(v_a_3532_);
v___x_3534_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3535_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3522_, v_name_3523_, v_k_3525_, v___x_3533_, v___x_3534_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
return v___x_3535_;
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec_ref(v_k_3525_);
lean_dec(v_name_3523_);
lean_dec_ref(v_argsPacker_3522_);
v_a_3536_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3531_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3531_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object* v_argsPacker_3544_, lean_object* v_name_3545_, lean_object* v_type_3546_, lean_object* v_k_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3544_, v_name_3545_, v_type_3546_, v_k_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object* v_00_u03b1_3554_, lean_object* v_argsPacker_3555_, lean_object* v_name_3556_, lean_object* v_type_3557_, lean_object* v_k_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3555_, v_name_3556_, v_type_3557_, v_k_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object* v_00_u03b1_3565_, lean_object* v_argsPacker_3566_, lean_object* v_name_3567_, lean_object* v_type_3568_, lean_object* v_k_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(v_00_u03b1_3565_, v_argsPacker_3566_, v_name_3567_, v_type_3568_, v_k_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object* v_argsPacker_3576_, lean_object* v_packedMotiveType_3577_, lean_object* v_type_3578_, lean_object* v_value_3579_, lean_object* v_k_3580_, lean_object* v_motives_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3576_, v_packedMotiveType_3577_, v_motives_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc_n(v_a_3588_, 2);
lean_dec_ref_known(v___x_3587_, 1);
v___x_3589_ = lean_unsigned_to_nat(1u);
v___x_3590_ = lean_mk_empty_array_with_capacity(v___x_3589_);
v___x_3591_ = lean_array_push(v___x_3590_, v_a_3588_);
v___x_3592_ = l_Lean_Meta_instantiateForall(v_type_3578_, v___x_3591_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec_ref(v___x_3591_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3594_ = l_Lean_Expr_app___override(v_value_3579_, v_a_3588_);
lean_inc(v___y_3585_);
lean_inc_ref(v___y_3584_);
lean_inc(v___y_3583_);
lean_inc_ref(v___y_3582_);
v___x_3595_ = lean_apply_8(v_k_3580_, v_motives_3581_, v___x_3594_, v_a_3593_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, lean_box(0));
return v___x_3595_;
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_a_3588_);
lean_dec_ref(v_motives_3581_);
lean_dec_ref(v_k_3580_);
lean_dec_ref(v_value_3579_);
v_a_3596_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3592_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3592_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec_ref(v_motives_3581_);
lean_dec_ref(v_k_3580_);
lean_dec_ref(v_value_3579_);
lean_dec_ref(v_type_3578_);
v_a_3604_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3587_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3587_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object* v_argsPacker_3612_, lean_object* v_packedMotiveType_3613_, lean_object* v_type_3614_, lean_object* v_value_3615_, lean_object* v_k_3616_, lean_object* v_motives_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3612_, v_packedMotiveType_3613_, v_type_3614_, v_value_3615_, v_k_3616_, v_motives_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec_ref(v_argsPacker_3612_);
return v_res_3623_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0));
v___x_3626_ = l_Lean_stringToMessageData(v___x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2));
v___x_3629_ = l_Lean_stringToMessageData(v___x_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object* v_argsPacker_3630_, lean_object* v_value_3631_, lean_object* v_type_3632_, lean_object* v_k_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; uint8_t v___x_3668_; 
v___x_3668_ = l_Lean_Expr_isForall(v_type_3632_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec_ref(v_k_3633_);
lean_dec_ref(v_value_3631_);
lean_dec_ref(v_argsPacker_3630_);
v___x_3669_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3);
v___x_3670_ = l_Lean_MessageData_ofExpr(v_type_3632_);
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3669_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3671_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
else
{
v___y_3649_ = v_a_3634_;
v___y_3650_ = v_a_3635_;
v___y_3651_ = v_a_3636_;
v___y_3652_ = v_a_3637_;
goto v___jp_3648_;
}
v___jp_3639_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = l_Lean_Expr_bindingName_x21(v_type_3632_);
lean_dec_ref(v_type_3632_);
v___x_3647_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3630_, v___x_3646_, v___y_3641_, v___y_3640_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
return v___x_3647_;
}
v___jp_3648_:
{
lean_object* v_packedMotiveType_3653_; lean_object* v___f_3654_; uint8_t v___x_3655_; 
v_packedMotiveType_3653_ = l_Lean_Expr_bindingDomain_x21(v_type_3632_);
lean_inc_ref(v_type_3632_);
lean_inc_ref(v_packedMotiveType_3653_);
lean_inc_ref(v_argsPacker_3630_);
v___f_3654_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3654_, 0, v_argsPacker_3630_);
lean_closure_set(v___f_3654_, 1, v_packedMotiveType_3653_);
lean_closure_set(v___f_3654_, 2, v_type_3632_);
lean_closure_set(v___f_3654_, 3, v_value_3631_);
lean_closure_set(v___f_3654_, 4, v_k_3633_);
v___x_3655_ = l_Lean_Expr_isForall(v_packedMotiveType_3653_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec_ref(v___f_3654_);
lean_dec_ref(v_type_3632_);
lean_dec_ref(v_argsPacker_3630_);
v___x_3656_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1);
v___x_3657_ = l_Lean_indentExpr(v_packedMotiveType_3653_);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3658_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
else
{
v___y_3640_ = v___f_3654_;
v___y_3641_ = v_packedMotiveType_3653_;
v___y_3642_ = v___y_3649_;
v___y_3643_ = v___y_3650_;
v___y_3644_ = v___y_3651_;
v___y_3645_ = v___y_3652_;
goto v___jp_3639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object* v_argsPacker_3681_, lean_object* v_value_3682_, lean_object* v_type_3683_, lean_object* v_k_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3681_, v_value_3682_, v_type_3683_, v_k_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object* v_00_u03b1_3691_, lean_object* v_argsPacker_3692_, lean_object* v_value_3693_, lean_object* v_type_3694_, lean_object* v_k_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3692_, v_value_3693_, v_type_3694_, v_k_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object* v_00_u03b1_3702_, lean_object* v_argsPacker_3703_, lean_object* v_value_3704_, lean_object* v_type_3705_, lean_object* v_k_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_Meta_ArgsPacker_curryParam(v_00_u03b1_3702_, v_argsPacker_3703_, v_value_3704_, v_type_3705_, v_k_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
return v_res_3712_;
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
