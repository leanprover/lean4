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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_16_; uint8_t v___x_17_; lean_object* v_a_18_; lean_object* v___x_19_; 
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_nat_dec_eq(v___x_4_, v___x_16_);
v_a_18_ = lean_array_uget_borrowed(v_as_5_, v_i_7_);
lean_inc(v___y_12_);
lean_inc_ref(v___y_11_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v_a_18_);
v___x_19_ = lean_infer_type(v_a_18_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_50_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_50_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_50_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_50_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; 
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_mk_empty_array_with_capacity(v___x_24_);
lean_inc(v_a_18_);
v___x_26_ = lean_array_push(v___x_25_, v_a_18_);
v___x_27_ = 1;
v___x_28_ = l_Lean_Meta_mkLambdaFVars(v___x_26_, v_b_8_, v___x_17_, v___x_14_, v___x_17_, v___x_14_, v___x_27_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
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
lean_ctor_set(v___x_31_, 0, v_a_20_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_20_);
v___x_35_ = v_reuseFailAlloc_48_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set_tag(v___x_22_, 1);
lean_ctor_set(v___x_22_, 0, v_a_29_);
v___x_37_ = v___x_22_;
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
lean_del_object(v___x_22_);
lean_dec(v_a_20_);
return v___x_28_;
}
}
}
else
{
lean_dec_ref(v_b_8_);
return v___x_19_;
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
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; 
v___x_539_ = lean_box(v___x_523_);
v___x_540_ = lean_box(v___x_524_);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_541_, 0, v___x_535_);
lean_closure_set(v___f_541_, 1, v_type_522_);
lean_closure_set(v___f_541_, 2, v___x_539_);
lean_closure_set(v___f_541_, 3, v___x_540_);
v___x_542_ = l_Lean_Meta_ArgsPacker_Unary_packType(v_xs_528_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_dec_eq(v___x_535_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_547_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_546_, v_a_543_, v___f_541_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_array_get_borrowed(v___x_525_, v_varNames_526_, v___x_527_);
lean_inc(v___x_548_);
v___x_549_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_548_, v_a_543_, v___f_541_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v___x_549_;
}
}
else
{
lean_dec_ref(v___f_541_);
return v___x_542_;
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
lean_object* v___x_646_; lean_object* v_env_647_; uint8_t v___x_648_; lean_object* v_env_649_; lean_object* v___x_650_; lean_object* v_toCold_651_; lean_object* v_mctx_652_; lean_object* v_lctx_653_; lean_object* v_options_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_646_ = lean_st_ref_get(v___y_644_);
v_env_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc_ref(v_env_647_);
lean_dec(v___x_646_);
v___x_648_ = 0;
v_env_649_ = l_Lean_Environment_setRecordingDeps(v_env_647_, v___x_648_);
v___x_650_ = lean_st_ref_get(v___y_642_);
v_toCold_651_ = lean_ctor_get(v___y_643_, 0);
v_mctx_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_mctx_652_);
lean_dec(v___x_650_);
v_lctx_653_ = lean_ctor_get(v___y_641_, 2);
v_options_654_ = lean_ctor_get(v_toCold_651_, 2);
lean_inc_ref(v_options_654_);
lean_inc_ref(v_lctx_653_);
v___x_655_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_655_, 0, v_env_649_);
lean_ctor_set(v___x_655_, 1, v_mctx_652_);
lean_ctor_set(v___x_655_, 2, v_lctx_653_);
lean_ctor_set(v___x_655_, 3, v_options_654_);
v___x_656_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v_msgData_640_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0___boxed(lean_object* v_msgData_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msgData_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_ref_671_; lean_object* v___x_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
v_ref_671_ = lean_ctor_get(v___y_668_, 2);
v___x_672_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_681_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_inc(v_ref_671_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_ref_671_);
lean_ctor_set(v___x_677_, 1, v_a_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 1);
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg___boxed(lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_688_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed(lean_object** _args){
lean_object* v___x_692_ = _args[0];
lean_object* v___x_693_ = _args[1];
lean_object* v___x_694_ = _args[2];
lean_object* v_arg_695_ = _args[3];
lean_object* v_arg_696_ = _args[4];
lean_object* v_a_697_ = _args[5];
lean_object* v_alt_698_ = _args[6];
lean_object* v_tail_699_ = _args[7];
lean_object* v_u_700_ = _args[8];
lean_object* v___x_701_ = _args[9];
lean_object* v___x_702_ = _args[10];
lean_object* v___x_703_ = _args[11];
lean_object* v_head_704_ = _args[12];
lean_object* v_x_705_ = _args[13];
lean_object* v___y_706_ = _args[14];
lean_object* v___y_707_ = _args[15];
lean_object* v___y_708_ = _args[16];
lean_object* v___y_709_ = _args[17];
lean_object* v___y_710_ = _args[18];
_start:
{
uint8_t v___x_2862__boxed_711_; uint8_t v___x_2863__boxed_712_; uint8_t v___x_2864__boxed_713_; lean_object* v_res_714_; 
v___x_2862__boxed_711_ = lean_unbox(v___x_701_);
v___x_2863__boxed_712_ = lean_unbox(v___x_702_);
v___x_2864__boxed_713_ = lean_unbox(v___x_703_);
v_res_714_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(v___x_692_, v___x_693_, v___x_694_, v_arg_695_, v_arg_696_, v_a_697_, v_alt_698_, v_tail_699_, v_u_700_, v___x_2862__boxed_711_, v___x_2863__boxed_712_, v___x_2864__boxed_713_, v_head_704_, v_x_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(lean_object* v_varNames_719_, lean_object* v_e_720_, lean_object* v_u_721_, lean_object* v_codomain_722_, lean_object* v_alt_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
if (lean_obj_tag(v_varNames_719_) == 0)
{
lean_object* v___x_729_; 
lean_dec_ref(v_codomain_722_);
lean_dec(v_u_721_);
lean_dec_ref(v_e_720_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_alt_723_);
return v___x_729_;
}
else
{
lean_object* v_tail_730_; 
v_tail_730_ = lean_ctor_get(v_varNames_719_, 1);
lean_inc(v_tail_730_);
if (lean_obj_tag(v_tail_730_) == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref_known(v_varNames_719_, 2);
lean_dec_ref(v_codomain_722_);
lean_dec(v_u_721_);
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_mk_empty_array_with_capacity(v___x_731_);
v___x_733_ = lean_array_push(v___x_732_, v_e_720_);
v___x_734_ = l_Lean_Expr_beta(v_alt_723_, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v_head_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_792_; 
v_head_736_ = lean_ctor_get(v_varNames_719_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_varNames_719_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_varNames_719_, 1);
lean_dec(v_unused_793_);
v___x_738_ = v_varNames_719_;
v_isShared_739_ = v_isSharedCheck_792_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_head_736_);
lean_dec(v_varNames_719_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_792_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_head_740_; lean_object* v___x_741_; 
v_head_740_ = lean_ctor_get(v_tail_730_, 0);
lean_inc(v_head_740_);
lean_inc(v_a_727_);
lean_inc_ref(v_a_726_);
lean_inc(v_a_725_);
lean_inc_ref(v_a_724_);
lean_inc_ref(v_e_720_);
v___x_741_ = lean_infer_type(v_e_720_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___x_752_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc_n(v_a_742_, 2);
lean_dec_ref_known(v___x_741_, 1);
v___x_752_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_742_, v_a_725_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = l_Lean_Expr_cleanupAnnotations(v_a_753_);
v___x_755_ = l_Lean_Expr_isApp(v___x_754_);
if (v___x_755_ == 0)
{
lean_dec_ref(v___x_754_);
lean_dec(v_head_740_);
lean_del_object(v___x_738_);
lean_dec(v_head_736_);
lean_dec_ref_known(v_tail_730_, 2);
lean_dec_ref(v_alt_723_);
lean_dec_ref(v_codomain_722_);
lean_dec(v_u_721_);
lean_dec_ref(v_e_720_);
v___y_744_ = v_a_724_;
v___y_745_ = v_a_725_;
v___y_746_ = v_a_726_;
v___y_747_ = v_a_727_;
goto v___jp_743_;
}
else
{
lean_object* v_arg_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_arg_756_ = lean_ctor_get(v___x_754_, 1);
lean_inc_ref(v_arg_756_);
v___x_757_ = l_Lean_Expr_appFnCleanup___redArg(v___x_754_);
v___x_758_ = l_Lean_Expr_isApp(v___x_757_);
if (v___x_758_ == 0)
{
lean_dec_ref(v___x_757_);
lean_dec_ref(v_arg_756_);
lean_dec(v_head_740_);
lean_del_object(v___x_738_);
lean_dec_ref_known(v_tail_730_, 2);
lean_dec(v_head_736_);
lean_dec_ref(v_alt_723_);
lean_dec_ref(v_codomain_722_);
lean_dec(v_u_721_);
lean_dec_ref(v_e_720_);
v___y_744_ = v_a_724_;
v___y_745_ = v_a_725_;
v___y_746_ = v_a_726_;
v___y_747_ = v_a_727_;
goto v___jp_743_;
}
else
{
lean_object* v_arg_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_arg_759_ = lean_ctor_get(v___x_757_, 1);
lean_inc_ref(v_arg_759_);
v___x_760_ = l_Lean_Expr_appFnCleanup___redArg(v___x_757_);
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0));
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_763_ = l_Lean_Expr_isConstOf(v___x_760_, v___x_762_);
lean_dec_ref(v___x_760_);
if (v___x_763_ == 0)
{
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
lean_dec(v_head_740_);
lean_del_object(v___x_738_);
lean_dec(v_head_736_);
lean_dec_ref_known(v_tail_730_, 2);
lean_dec_ref(v_alt_723_);
lean_dec_ref(v_codomain_722_);
lean_dec(v_u_721_);
lean_dec_ref(v_e_720_);
v___y_744_ = v_a_724_;
v___y_745_ = v_a_725_;
v___y_746_ = v_a_726_;
v___y_747_ = v_a_727_;
goto v___jp_743_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; 
v___x_764_ = l_Lean_Expr_getAppFn(v_a_742_);
lean_dec(v_a_742_);
v___x_765_ = l_Lean_Expr_constLevels_x21(v___x_764_);
lean_dec_ref(v___x_764_);
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_mk_empty_array_with_capacity(v___x_766_);
lean_inc_ref(v_e_720_);
lean_inc_ref(v___x_767_);
v___x_768_ = lean_array_push(v___x_767_, v_e_720_);
v___x_769_ = 0;
v___x_770_ = 1;
v___x_771_ = l_Lean_Meta_mkLambdaFVars(v___x_768_, v_codomain_722_, v___x_769_, v___x_763_, v___x_769_, v___x_763_, v___x_770_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec_ref(v___x_768_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_n(v_a_772_, 2);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = lean_box(v___x_769_);
v___x_774_ = lean_box(v___x_763_);
v___x_775_ = lean_box(v___x_770_);
lean_inc(v_u_721_);
lean_inc_ref(v_arg_756_);
lean_inc_ref_n(v_arg_759_, 2);
lean_inc(v___x_765_);
v___f_776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed), 19, 13);
lean_closure_set(v___f_776_, 0, v___x_767_);
lean_closure_set(v___f_776_, 1, v___x_761_);
lean_closure_set(v___f_776_, 2, v___x_765_);
lean_closure_set(v___f_776_, 3, v_arg_759_);
lean_closure_set(v___f_776_, 4, v_arg_756_);
lean_closure_set(v___f_776_, 5, v_a_772_);
lean_closure_set(v___f_776_, 6, v_alt_723_);
lean_closure_set(v___f_776_, 7, v_tail_730_);
lean_closure_set(v___f_776_, 8, v_u_721_);
lean_closure_set(v___f_776_, 9, v___x_773_);
lean_closure_set(v___f_776_, 10, v___x_774_);
lean_closure_set(v___f_776_, 11, v___x_775_);
lean_closure_set(v___f_776_, 12, v_head_740_);
v___x_777_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_736_, v_arg_759_, v___f_776_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_791_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_791_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_791_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_791_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3));
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_765_);
lean_ctor_set(v___x_738_, 0, v_u_721_);
v___x_784_ = v___x_738_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_u_721_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_765_);
v___x_784_ = v_reuseFailAlloc_790_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = l_Lean_Expr_const___override(v___x_782_, v___x_784_);
v___x_786_ = l_Lean_mkApp5(v___x_785_, v_arg_759_, v_arg_756_, v_a_772_, v_e_720_, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_786_);
v___x_788_ = v___x_780_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_dec(v_a_772_);
lean_dec(v___x_765_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
lean_del_object(v___x_738_);
lean_dec(v_u_721_);
lean_dec_ref(v_e_720_);
return v___x_777_;
}
}
else
{
lean_dec_ref(v___x_767_);
lean_dec(v___x_765_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
lean_dec(v_head_740_);
lean_del_object(v___x_738_);
lean_dec_ref_known(v_tail_730_, 2);
lean_dec(v_head_736_);
lean_dec_ref(v_alt_723_);
lean_dec(v_u_721_);
lean_dec_ref(v_e_720_);
return v___x_771_;
}
}
}
}
}
else
{
lean_dec(v_a_742_);
lean_dec(v_head_740_);
lean_del_object(v___x_738_);
lean_dec_ref_known(v_tail_730_, 2);
lean_dec(v_head_736_);
lean_dec_ref(v_alt_723_);
lean_dec_ref(v_codomain_722_);
lean_dec(v_u_721_);
lean_dec_ref(v_e_720_);
return v___x_752_;
}
v___jp_743_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_748_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1);
v___x_749_ = l_Lean_MessageData_ofExpr(v_a_742_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_750_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
return v___x_751_;
}
}
else
{
lean_dec(v_head_740_);
lean_del_object(v___x_738_);
lean_dec(v_head_736_);
lean_dec_ref_known(v_tail_730_, 2);
lean_dec_ref(v_alt_723_);
lean_dec_ref(v_codomain_722_);
lean_dec(v_u_721_);
lean_dec_ref(v_e_720_);
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(lean_object* v___x_794_, lean_object* v___x_795_, lean_object* v_arg_796_, lean_object* v_arg_797_, lean_object* v_x_798_, lean_object* v___x_799_, lean_object* v_a_800_, lean_object* v_alt_801_, lean_object* v___x_802_, lean_object* v_tail_803_, lean_object* v_u_804_, uint8_t v___x_805_, uint8_t v___x_806_, uint8_t v___x_807_, lean_object* v_y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_814_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6));
v___x_815_ = l_Lean_Name_mkStr2(v___x_794_, v___x_814_);
v___x_816_ = l_Lean_Expr_const___override(v___x_815_, v___x_795_);
lean_inc_ref_n(v_y_808_, 2);
lean_inc_ref(v_x_798_);
v___x_817_ = l_Lean_mkApp4(v___x_816_, v_arg_796_, v_arg_797_, v_x_798_, v_y_808_);
v___x_818_ = lean_array_push(v___x_799_, v___x_817_);
v___x_819_ = l_Lean_Expr_beta(v_a_800_, v___x_818_);
v___x_820_ = l_Lean_Expr_beta(v_alt_801_, v___x_802_);
v___x_821_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_tail_803_, v_y_808_, v_u_804_, v___x_819_, v___x_820_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = lean_unsigned_to_nat(2u);
v___x_824_ = lean_mk_empty_array_with_capacity(v___x_823_);
v___x_825_ = lean_array_push(v___x_824_, v_x_798_);
v___x_826_ = lean_array_push(v___x_825_, v_y_808_);
v___x_827_ = l_Lean_Meta_mkLambdaFVars(v___x_826_, v_a_822_, v___x_805_, v___x_806_, v___x_805_, v___x_806_, v___x_807_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec_ref(v___x_826_);
return v___x_827_;
}
else
{
lean_dec_ref(v_y_808_);
lean_dec_ref(v_x_798_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_828_ = _args[0];
lean_object* v___x_829_ = _args[1];
lean_object* v_arg_830_ = _args[2];
lean_object* v_arg_831_ = _args[3];
lean_object* v_x_832_ = _args[4];
lean_object* v___x_833_ = _args[5];
lean_object* v_a_834_ = _args[6];
lean_object* v_alt_835_ = _args[7];
lean_object* v___x_836_ = _args[8];
lean_object* v_tail_837_ = _args[9];
lean_object* v_u_838_ = _args[10];
lean_object* v___x_839_ = _args[11];
lean_object* v___x_840_ = _args[12];
lean_object* v___x_841_ = _args[13];
lean_object* v_y_842_ = _args[14];
lean_object* v___y_843_ = _args[15];
lean_object* v___y_844_ = _args[16];
lean_object* v___y_845_ = _args[17];
lean_object* v___y_846_ = _args[18];
lean_object* v___y_847_ = _args[19];
_start:
{
uint8_t v___x_2883__boxed_848_; uint8_t v___x_2884__boxed_849_; uint8_t v___x_2885__boxed_850_; lean_object* v_res_851_; 
v___x_2883__boxed_848_ = lean_unbox(v___x_839_);
v___x_2884__boxed_849_ = lean_unbox(v___x_840_);
v___x_2885__boxed_850_ = lean_unbox(v___x_841_);
v_res_851_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(v___x_828_, v___x_829_, v_arg_830_, v_arg_831_, v_x_832_, v___x_833_, v_a_834_, v_alt_835_, v___x_836_, v_tail_837_, v_u_838_, v___x_2883__boxed_848_, v___x_2884__boxed_849_, v___x_2885__boxed_850_, v_y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v___x_854_, lean_object* v_arg_855_, lean_object* v_arg_856_, lean_object* v_a_857_, lean_object* v_alt_858_, lean_object* v_tail_859_, lean_object* v_u_860_, uint8_t v___x_861_, uint8_t v___x_862_, uint8_t v___x_863_, lean_object* v_head_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc_ref(v_x_865_);
lean_inc_ref(v___x_852_);
v___x_871_ = lean_array_push(v___x_852_, v_x_865_);
v___x_872_ = lean_box(v___x_861_);
v___x_873_ = lean_box(v___x_862_);
v___x_874_ = lean_box(v___x_863_);
lean_inc_ref(v___x_871_);
lean_inc_ref(v_arg_856_);
v___f_875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed), 20, 14);
lean_closure_set(v___f_875_, 0, v___x_853_);
lean_closure_set(v___f_875_, 1, v___x_854_);
lean_closure_set(v___f_875_, 2, v_arg_855_);
lean_closure_set(v___f_875_, 3, v_arg_856_);
lean_closure_set(v___f_875_, 4, v_x_865_);
lean_closure_set(v___f_875_, 5, v___x_852_);
lean_closure_set(v___f_875_, 6, v_a_857_);
lean_closure_set(v___f_875_, 7, v_alt_858_);
lean_closure_set(v___f_875_, 8, v___x_871_);
lean_closure_set(v___f_875_, 9, v_tail_859_);
lean_closure_set(v___f_875_, 10, v_u_860_);
lean_closure_set(v___f_875_, 11, v___x_872_);
lean_closure_set(v___f_875_, 12, v___x_873_);
lean_closure_set(v___f_875_, 13, v___x_874_);
v___x_876_ = l_Lean_Expr_beta(v_arg_856_, v___x_871_);
v___x_877_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_864_, v___x_876_, v___f_875_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___boxed(lean_object* v_varNames_878_, lean_object* v_e_879_, lean_object* v_u_880_, lean_object* v_codomain_881_, lean_object* v_alt_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_varNames_878_, v_e_879_, v_u_880_, v_codomain_881_, v_alt_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(lean_object* v_00_u03b1_889_, lean_object* v_msg_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___boxed(lean_object* v_00_u03b1_897_, lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(v_00_u03b1_897_, v_msg_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_904_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_907_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_908_ = lean_unsigned_to_nat(23u);
v___x_909_ = lean_unsigned_to_nat(180u);
v___x_910_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0));
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_912_ = l_mkPanicMessageWithDecl(v___x_911_, v___x_910_, v___x_909_, v___x_908_, v___x_907_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_varNames_915_, lean_object* v_e_916_, uint8_t v___x_917_, uint8_t v___x_918_, lean_object* v_xs_919_, lean_object* v_codomain_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_array_get_size(v_xs_919_);
v___x_927_ = lean_nat_dec_eq(v___x_926_, v___x_913_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec_ref(v_codomain_920_);
lean_dec_ref(v_e_916_);
lean_dec_ref(v_varNames_915_);
v___x_928_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2);
v___x_929_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_928_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_array_fget_borrowed(v_xs_919_, v___x_914_);
lean_inc_ref(v_codomain_920_);
v___x_931_ = l_Lean_Meta_getLevel(v_codomain_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = lean_array_to_list(v_varNames_915_);
lean_inc(v___x_930_);
v___x_934_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v___x_933_, v___x_930_, v_a_932_, v_codomain_920_, v_e_916_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_913_);
lean_inc(v___x_930_);
v___x_937_ = lean_array_push(v___x_936_, v___x_930_);
v___x_938_ = 1;
v___x_939_ = l_Lean_Meta_mkLambdaFVars(v___x_937_, v_a_935_, v___x_917_, v___x_918_, v___x_917_, v___x_918_, v___x_938_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec_ref(v___x_937_);
return v___x_939_;
}
else
{
return v___x_934_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_codomain_920_);
lean_dec_ref(v_e_916_);
lean_dec_ref(v_varNames_915_);
v_a_940_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_931_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_931_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed(lean_object* v___x_948_, lean_object* v___x_949_, lean_object* v_varNames_950_, lean_object* v_e_951_, lean_object* v___x_952_, lean_object* v___x_953_, lean_object* v_xs_954_, lean_object* v_codomain_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_799__boxed_961_; uint8_t v___x_800__boxed_962_; lean_object* v_res_963_; 
v___x_799__boxed_961_ = lean_unbox(v___x_952_);
v___x_800__boxed_962_ = lean_unbox(v___x_953_);
v_res_963_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(v___x_948_, v___x_949_, v_varNames_950_, v_e_951_, v___x_799__boxed_961_, v___x_800__boxed_962_, v_xs_954_, v_codomain_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v_xs_954_);
lean_dec(v___x_949_);
lean_dec(v___x_948_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry(lean_object* v_varNames_969_, lean_object* v_e_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_976_ = lean_array_get_size(v_varNames_969_);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_nat_dec_eq(v___x_976_, v___x_977_);
if (v___x_978_ == 0)
{
uint8_t v___x_979_; lean_object* v___x_980_; 
v___x_979_ = 1;
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc_ref(v_e_970_);
v___x_980_ = lean_infer_type(v_e_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
lean_inc_ref(v_varNames_969_);
v___x_982_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_969_, v_a_981_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_box(v___x_978_);
v___x_986_ = lean_box(v___x_979_);
v___f_987_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed), 13, 6);
lean_closure_set(v___f_987_, 0, v___x_984_);
lean_closure_set(v___f_987_, 1, v___x_977_);
lean_closure_set(v___f_987_, 2, v_varNames_969_);
lean_closure_set(v___f_987_, 3, v_e_970_);
lean_closure_set(v___f_987_, 4, v___x_985_);
lean_closure_set(v___f_987_, 5, v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_989_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_983_, v___x_988_, v___f_987_, v___x_978_, v___x_978_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_989_;
}
else
{
lean_dec_ref(v_e_970_);
lean_dec_ref(v_varNames_969_);
return v___x_982_;
}
}
else
{
lean_dec_ref(v_e_970_);
lean_dec_ref(v_varNames_969_);
return v___x_980_;
}
}
else
{
lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec_ref(v_varNames_969_);
v___x_990_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_991_ = 0;
v___x_992_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_993_ = l_Lean_mkLambda(v___x_990_, v___x_991_, v___x_992_, v_e_970_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___boxed(lean_object* v_varNames_995_, lean_object* v_e_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_varNames_995_, v_e_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
return v_res_1002_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_dummy_1008_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1));
v_dummy_1008_ = l_Lean_Expr_const___override(v___x_1007_, v___x_1006_);
return v_dummy_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(lean_object* v_args_1009_, lean_object* v_type_1010_, lean_object* v_packedDomain_1011_, lean_object* v_tail_1012_, lean_object* v_x_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_dummy_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_dummy_1019_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1013_);
v___x_1020_ = lean_array_push(v_args_1009_, v_x_1013_);
v___x_1021_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1010_, v_packedDomain_1011_, v_dummy_1019_, v___x_1020_, v_tail_1012_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; uint8_t v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_mk_empty_array_with_capacity(v___x_1023_);
v___x_1025_ = lean_array_push(v___x_1024_, v_x_1013_);
v___x_1026_ = 0;
v___x_1027_ = 1;
v___x_1028_ = 1;
v___x_1029_ = l_Lean_Meta_mkForallFVars(v___x_1025_, v_a_1022_, v___x_1026_, v___x_1027_, v___x_1027_, v___x_1028_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec_ref(v___x_1025_);
return v___x_1029_;
}
else
{
lean_dec_ref(v_x_1013_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed(lean_object* v_args_1030_, lean_object* v_type_1031_, lean_object* v_packedDomain_1032_, lean_object* v_tail_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(v_args_1030_, v_type_1031_, v_packedDomain_1032_, v_tail_1033_, v_x_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed(lean_object* v_arg_1041_, lean_object* v_args_1042_, lean_object* v_type_1043_, lean_object* v_packedDomain_1044_, lean_object* v_tail_1045_, lean_object* v___x_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v___x_644__boxed_1053_; lean_object* v_res_1054_; 
v___x_644__boxed_1053_ = lean_unbox(v___x_1046_);
v_res_1054_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(v_arg_1041_, v_args_1042_, v_type_1043_, v_packedDomain_1044_, v_tail_1045_, v___x_644__boxed_1053_, v_x_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(lean_object* v_type_1055_, lean_object* v_packedDomain_1056_, lean_object* v_domain_1057_, lean_object* v_args_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; 
if (lean_obj_tag(v_a_1059_) == 0)
{
lean_object* v_packedArg_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec_ref(v_domain_1057_);
v_packedArg_1074_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1056_, v_args_1058_);
lean_dec_ref(v_args_1058_);
lean_dec_ref(v_packedDomain_1056_);
v___x_1075_ = lean_unsigned_to_nat(1u);
v___x_1076_ = lean_mk_empty_array_with_capacity(v___x_1075_);
v___x_1077_ = lean_array_push(v___x_1076_, v_packedArg_1074_);
v___x_1078_ = l_Lean_Meta_instantiateForall(v_type_1055_, v___x_1077_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec_ref(v___x_1077_);
return v___x_1078_;
}
else
{
lean_object* v_tail_1079_; 
v_tail_1079_ = lean_ctor_get(v_a_1059_, 1);
lean_inc(v_tail_1079_);
if (lean_obj_tag(v_tail_1079_) == 0)
{
lean_object* v_head_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; 
v_head_1080_ = lean_ctor_get(v_a_1059_, 0);
lean_inc(v_head_1080_);
lean_dec_ref_known(v_a_1059_, 2);
v___f_1081_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1081_, 0, v_args_1058_);
lean_closure_set(v___f_1081_, 1, v_type_1055_);
lean_closure_set(v___f_1081_, 2, v_packedDomain_1056_);
lean_closure_set(v___f_1081_, 3, v_tail_1079_);
v___x_1082_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1080_, v_domain_1057_, v___f_1081_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1082_;
}
else
{
lean_object* v_head_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_head_1083_ = lean_ctor_get(v_a_1059_, 0);
lean_inc(v_head_1083_);
lean_dec_ref_known(v_a_1059_, 2);
lean_inc_ref(v_domain_1057_);
v___x_1084_ = l_Lean_Expr_cleanupAnnotations(v_domain_1057_);
v___x_1085_ = l_Lean_Expr_isApp(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v___x_1084_);
lean_dec(v_head_1083_);
lean_dec(v_tail_1079_);
lean_dec_ref(v_args_1058_);
lean_dec_ref(v_packedDomain_1056_);
lean_dec_ref(v_type_1055_);
v___y_1066_ = v_a_1060_;
v___y_1067_ = v_a_1061_;
v___y_1068_ = v_a_1062_;
v___y_1069_ = v_a_1063_;
goto v___jp_1065_;
}
else
{
lean_object* v_arg_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_arg_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc_ref(v_arg_1086_);
v___x_1087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1084_);
v___x_1088_ = l_Lean_Expr_isApp(v___x_1087_);
if (v___x_1088_ == 0)
{
lean_dec_ref(v___x_1087_);
lean_dec_ref(v_arg_1086_);
lean_dec(v_head_1083_);
lean_dec(v_tail_1079_);
lean_dec_ref(v_args_1058_);
lean_dec_ref(v_packedDomain_1056_);
lean_dec_ref(v_type_1055_);
v___y_1066_ = v_a_1060_;
v___y_1067_ = v_a_1061_;
v___y_1068_ = v_a_1062_;
v___y_1069_ = v_a_1063_;
goto v___jp_1065_;
}
else
{
lean_object* v_arg_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_arg_1089_ = lean_ctor_get(v___x_1087_, 1);
lean_inc_ref(v_arg_1089_);
v___x_1090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1087_);
v___x_1091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1092_ = l_Lean_Expr_isConstOf(v___x_1090_, v___x_1091_);
lean_dec_ref(v___x_1090_);
if (v___x_1092_ == 0)
{
lean_dec_ref(v_arg_1089_);
lean_dec_ref(v_arg_1086_);
lean_dec(v_head_1083_);
lean_dec(v_tail_1079_);
lean_dec_ref(v_args_1058_);
lean_dec_ref(v_packedDomain_1056_);
lean_dec_ref(v_type_1055_);
v___y_1066_ = v_a_1060_;
v___y_1067_ = v_a_1061_;
v___y_1068_ = v_a_1062_;
v___y_1069_ = v_a_1063_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; 
lean_dec_ref(v_domain_1057_);
v___x_1093_ = lean_box(v___x_1092_);
v___f_1094_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1094_, 0, v_arg_1086_);
lean_closure_set(v___f_1094_, 1, v_args_1058_);
lean_closure_set(v___f_1094_, 2, v_type_1055_);
lean_closure_set(v___f_1094_, 3, v_packedDomain_1056_);
lean_closure_set(v___f_1094_, 4, v_tail_1079_);
lean_closure_set(v___f_1094_, 5, v___x_1093_);
v___x_1095_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1083_, v_arg_1089_, v___f_1094_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1095_;
}
}
}
}
}
v___jp_1065_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1);
v___x_1071_ = l_Lean_MessageData_ofExpr(v_domain_1057_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1072_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(lean_object* v_arg_1096_, lean_object* v_args_1097_, lean_object* v_type_1098_, lean_object* v_packedDomain_1099_, lean_object* v_tail_1100_, uint8_t v___x_1101_, lean_object* v_x_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_mk_empty_array_with_capacity(v___x_1108_);
lean_inc_ref(v_x_1102_);
v___x_1110_ = lean_array_push(v___x_1109_, v_x_1102_);
lean_inc_ref(v___x_1110_);
v___x_1111_ = l_Lean_Expr_beta(v_arg_1096_, v___x_1110_);
v___x_1112_ = lean_array_push(v_args_1097_, v_x_1102_);
v___x_1113_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1098_, v_packedDomain_1099_, v___x_1111_, v___x_1112_, v_tail_1100_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; uint8_t v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = 0;
v___x_1116_ = 1;
v___x_1117_ = l_Lean_Meta_mkForallFVars(v___x_1110_, v_a_1114_, v___x_1115_, v___x_1101_, v___x_1101_, v___x_1116_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec_ref(v___x_1110_);
return v___x_1117_;
}
else
{
lean_dec_ref(v___x_1110_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___boxed(lean_object* v_type_1118_, lean_object* v_packedDomain_1119_, lean_object* v_domain_1120_, lean_object* v_args_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1118_, v_packedDomain_1119_, v_domain_1120_, v_args_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
return v_res_1128_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0));
v___x_1131_ = l_Lean_stringToMessageData(v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(lean_object* v_varNames_1132_, lean_object* v_type_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; uint8_t v___x_1148_; 
v___x_1148_ = l_Lean_Expr_isForall(v_type_1133_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_varNames_1132_);
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_1150_ = l_Lean_MessageData_ofExpr(v_type_1133_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1151_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
v___y_1140_ = v_a_1134_;
v___y_1141_ = v_a_1135_;
v___y_1142_ = v_a_1136_;
v___y_1143_ = v_a_1137_;
goto v___jp_1139_;
}
v___jp_1139_:
{
lean_object* v_packedDomain_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_packedDomain_1144_ = l_Lean_Expr_bindingDomain_x21(v_type_1133_);
v___x_1145_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1146_ = lean_array_to_list(v_varNames_1132_);
lean_inc_ref(v_packedDomain_1144_);
v___x_1147_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1133_, v_packedDomain_1144_, v_packedDomain_1144_, v___x_1145_, v___x_1146_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___boxed(lean_object* v_varNames_1161_, lean_object* v_type_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_varNames_1161_, v_type_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1168_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(lean_object* v_args_1172_, lean_object* v_e_1173_, lean_object* v_packedDomain_1174_, lean_object* v_tail_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_dummy_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_dummy_1182_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1176_);
v___x_1183_ = lean_array_push(v_args_1172_, v_x_1176_);
v___x_1184_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1173_, v_packedDomain_1174_, v_dummy_1182_, v___x_1183_, v_tail_1175_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; uint8_t v___x_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_mk_empty_array_with_capacity(v___x_1186_);
v___x_1188_ = lean_array_push(v___x_1187_, v_x_1176_);
v___x_1189_ = 0;
v___x_1190_ = 1;
v___x_1191_ = 1;
v___x_1192_ = l_Lean_Meta_mkLambdaFVars(v___x_1188_, v_a_1185_, v___x_1189_, v___x_1190_, v___x_1189_, v___x_1190_, v___x_1191_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec_ref(v___x_1188_);
return v___x_1192_;
}
else
{
lean_dec_ref(v_x_1176_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed(lean_object* v_args_1193_, lean_object* v_e_1194_, lean_object* v_packedDomain_1195_, lean_object* v_tail_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(v_args_1193_, v_e_1194_, v_packedDomain_1195_, v_tail_1196_, v_x_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed(lean_object* v_arg_1204_, lean_object* v_args_1205_, lean_object* v_e_1206_, lean_object* v_packedDomain_1207_, lean_object* v_tail_1208_, lean_object* v___x_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v___x_762__boxed_1216_; lean_object* v_res_1217_; 
v___x_762__boxed_1216_ = lean_unbox(v___x_1209_);
v_res_1217_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(v_arg_1204_, v_args_1205_, v_e_1206_, v_packedDomain_1207_, v_tail_1208_, v___x_762__boxed_1216_, v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(lean_object* v_e_1218_, lean_object* v_packedDomain_1219_, lean_object* v_domain_1220_, lean_object* v_args_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; 
if (lean_obj_tag(v_a_1222_) == 0)
{
lean_object* v_packedArg_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec_ref(v_domain_1220_);
v_packedArg_1237_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1219_, v_args_1221_);
lean_dec_ref(v_args_1221_);
lean_dec_ref(v_packedDomain_1219_);
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_mk_empty_array_with_capacity(v___x_1238_);
v___x_1240_ = lean_array_push(v___x_1239_, v_packedArg_1237_);
v___x_1241_ = l_Lean_Expr_beta(v_e_1218_, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
else
{
lean_object* v_tail_1243_; 
v_tail_1243_ = lean_ctor_get(v_a_1222_, 1);
lean_inc(v_tail_1243_);
if (lean_obj_tag(v_tail_1243_) == 0)
{
lean_object* v_head_1244_; lean_object* v___f_1245_; lean_object* v___x_1246_; 
v_head_1244_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_head_1244_);
lean_dec_ref_known(v_a_1222_, 2);
v___f_1245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1245_, 0, v_args_1221_);
lean_closure_set(v___f_1245_, 1, v_e_1218_);
lean_closure_set(v___f_1245_, 2, v_packedDomain_1219_);
lean_closure_set(v___f_1245_, 3, v_tail_1243_);
v___x_1246_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1244_, v_domain_1220_, v___f_1245_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
return v___x_1246_;
}
else
{
lean_object* v_head_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_head_1247_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_head_1247_);
lean_dec_ref_known(v_a_1222_, 2);
lean_inc_ref(v_domain_1220_);
v___x_1248_ = l_Lean_Expr_cleanupAnnotations(v_domain_1220_);
v___x_1249_ = l_Lean_Expr_isApp(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec_ref(v___x_1248_);
lean_dec(v_head_1247_);
lean_dec(v_tail_1243_);
lean_dec_ref(v_args_1221_);
lean_dec_ref(v_packedDomain_1219_);
lean_dec_ref(v_e_1218_);
v___y_1229_ = v_a_1223_;
v___y_1230_ = v_a_1224_;
v___y_1231_ = v_a_1225_;
v___y_1232_ = v_a_1226_;
goto v___jp_1228_;
}
else
{
lean_object* v_arg_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_arg_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc_ref(v_arg_1250_);
v___x_1251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1248_);
v___x_1252_ = l_Lean_Expr_isApp(v___x_1251_);
if (v___x_1252_ == 0)
{
lean_dec_ref(v___x_1251_);
lean_dec_ref(v_arg_1250_);
lean_dec(v_head_1247_);
lean_dec(v_tail_1243_);
lean_dec_ref(v_args_1221_);
lean_dec_ref(v_packedDomain_1219_);
lean_dec_ref(v_e_1218_);
v___y_1229_ = v_a_1223_;
v___y_1230_ = v_a_1224_;
v___y_1231_ = v_a_1225_;
v___y_1232_ = v_a_1226_;
goto v___jp_1228_;
}
else
{
lean_object* v_arg_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_arg_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc_ref(v_arg_1253_);
v___x_1254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1251_);
v___x_1255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1256_ = l_Lean_Expr_isConstOf(v___x_1254_, v___x_1255_);
lean_dec_ref(v___x_1254_);
if (v___x_1256_ == 0)
{
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
lean_dec(v_head_1247_);
lean_dec(v_tail_1243_);
lean_dec_ref(v_args_1221_);
lean_dec_ref(v_packedDomain_1219_);
lean_dec_ref(v_e_1218_);
v___y_1229_ = v_a_1223_;
v___y_1230_ = v_a_1224_;
v___y_1231_ = v_a_1225_;
v___y_1232_ = v_a_1226_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; 
lean_dec_ref(v_domain_1220_);
v___x_1257_ = lean_box(v___x_1256_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1258_, 0, v_arg_1250_);
lean_closure_set(v___f_1258_, 1, v_args_1221_);
lean_closure_set(v___f_1258_, 2, v_e_1218_);
lean_closure_set(v___f_1258_, 3, v_packedDomain_1219_);
lean_closure_set(v___f_1258_, 4, v_tail_1243_);
lean_closure_set(v___f_1258_, 5, v___x_1257_);
v___x_1259_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1247_, v_arg_1253_, v___f_1258_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
return v___x_1259_;
}
}
}
}
}
v___jp_1228_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1);
v___x_1234_ = l_Lean_MessageData_ofExpr(v_domain_1220_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1235_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(lean_object* v_arg_1260_, lean_object* v_args_1261_, lean_object* v_e_1262_, lean_object* v_packedDomain_1263_, lean_object* v_tail_1264_, uint8_t v___x_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_mk_empty_array_with_capacity(v___x_1272_);
lean_inc_ref(v_x_1266_);
v___x_1274_ = lean_array_push(v___x_1273_, v_x_1266_);
lean_inc_ref(v___x_1274_);
v___x_1275_ = l_Lean_Expr_beta(v_arg_1260_, v___x_1274_);
v___x_1276_ = lean_array_push(v_args_1261_, v_x_1266_);
v___x_1277_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1262_, v_packedDomain_1263_, v___x_1275_, v___x_1276_, v_tail_1264_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; uint8_t v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = 0;
v___x_1280_ = 1;
v___x_1281_ = l_Lean_Meta_mkLambdaFVars(v___x_1274_, v_a_1278_, v___x_1279_, v___x_1265_, v___x_1279_, v___x_1265_, v___x_1280_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec_ref(v___x_1274_);
return v___x_1281_;
}
else
{
lean_dec_ref(v___x_1274_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___boxed(lean_object* v_e_1282_, lean_object* v_packedDomain_1283_, lean_object* v_domain_1284_, lean_object* v_args_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1282_, v_packedDomain_1283_, v_domain_1284_, v_args_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
return v_res_1292_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1296_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_pack___closed__2, &l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_mk_empty_array_with_capacity(v___x_1297_);
v___x_1299_ = lean_array_push(v___x_1298_, v___x_1296_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(lean_object* v_varNames_1300_, lean_object* v_e_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = lean_array_get_size(v_varNames_1300_);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_nat_dec_eq(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_inc(v_a_1305_);
lean_inc_ref(v_a_1304_);
lean_inc(v_a_1303_);
lean_inc_ref(v_a_1302_);
lean_inc_ref(v_e_1301_);
v___x_1310_ = lean_infer_type(v_e_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1312_ = l_Lean_Meta_whnfForall(v_a_1311_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; uint8_t v___x_1323_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1323_ = l_Lean_Expr_isForall(v_a_1313_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_e_1301_);
lean_dec_ref(v_varNames_1300_);
v___x_1324_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1);
v___x_1325_ = l_Lean_MessageData_ofExpr(v_a_1313_);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1326_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
v___y_1315_ = v_a_1302_;
v___y_1316_ = v_a_1303_;
v___y_1317_ = v_a_1304_;
v___y_1318_ = v_a_1305_;
goto v___jp_1314_;
}
v___jp_1314_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = l_Lean_Expr_bindingDomain_x21(v_a_1313_);
lean_dec(v_a_1313_);
v___x_1320_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1321_ = lean_array_to_list(v_varNames_1300_);
lean_inc_ref(v___x_1319_);
v___x_1322_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1301_, v___x_1319_, v___x_1319_, v___x_1320_, v___x_1321_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1322_;
}
}
else
{
lean_dec_ref(v_e_1301_);
lean_dec_ref(v_varNames_1300_);
return v___x_1312_;
}
}
else
{
lean_dec_ref(v_e_1301_);
lean_dec_ref(v_varNames_1300_);
return v___x_1310_;
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec_ref(v_varNames_1300_);
v___x_1336_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2);
v___x_1337_ = l_Lean_Expr_beta(v_e_1301_, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___boxed(lean_object* v_varNames_1339_, lean_object* v_e_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v_varNames_1339_, v_e_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(lean_object* v_as_1350_, size_t v_sz_1351_, size_t v_i_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_usize_dec_lt(v_i_1352_, v_sz_1351_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_b_1353_);
return v___x_1360_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_a_1361_ = lean_array_uget_borrowed(v_as_1350_, v_i_1352_);
v___x_1362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1363_ = lean_unsigned_to_nat(2u);
v___x_1364_ = lean_mk_empty_array_with_capacity(v___x_1363_);
lean_inc(v_a_1361_);
v___x_1365_ = lean_array_push(v___x_1364_, v_a_1361_);
v___x_1366_ = lean_array_push(v___x_1365_, v_b_1353_);
v___x_1367_ = l_Lean_Meta_mkAppM(v___x_1362_, v___x_1366_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; size_t v___x_1369_; size_t v___x_1370_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_add(v_i_1352_, v___x_1369_);
v_i_1352_ = v___x_1370_;
v_b_1353_ = v_a_1368_;
goto _start;
}
else
{
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___boxed(lean_object* v_as_1372_, lean_object* v_sz_1373_, lean_object* v_i_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
size_t v_sz_boxed_1381_; size_t v_i_boxed_1382_; lean_object* v_res_1383_; 
v_sz_boxed_1381_ = lean_unbox_usize(v_sz_1373_);
lean_dec(v_sz_1373_);
v_i_boxed_1382_ = lean_unbox_usize(v_i_1374_);
lean_dec(v_i_1374_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v_as_1372_, v_sz_boxed_1381_, v_i_boxed_1382_, v_b_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v_as_1372_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object* v_ds_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_r_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v___x_1390_ = l_Lean_instInhabitedExpr;
v___x_1391_ = lean_array_get_size(v_ds_1384_);
v___x_1392_ = lean_unsigned_to_nat(1u);
v___x_1393_ = lean_nat_sub(v___x_1391_, v___x_1392_);
v_r_1394_ = lean_array_get(v___x_1390_, v_ds_1384_, v___x_1393_);
lean_dec(v___x_1393_);
v___x_1395_ = lean_array_pop(v_ds_1384_);
v___x_1396_ = l_Array_reverse___redArg(v___x_1395_);
v_sz_1397_ = lean_array_size(v___x_1396_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v___x_1396_, v_sz_1397_, v___x_1398_, v_r_1394_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
lean_dec_ref(v___x_1396_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object* v_ds_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v_ds_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1406_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0));
v___x_1409_ = l_Lean_stringToMessageData(v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object* v_n_1410_, lean_object* v_type_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v_zero_1426_; uint8_t v_isZero_1427_; 
v_zero_1426_ = lean_unsigned_to_nat(0u);
v_isZero_1427_ = lean_nat_dec_eq(v_n_1410_, v_zero_1426_);
if (v_isZero_1427_ == 1)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref(v_type_1411_);
v___x_1428_ = lean_box(0);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
else
{
lean_object* v_one_1430_; lean_object* v_n_1431_; uint8_t v___x_1432_; 
v_one_1430_ = lean_unsigned_to_nat(1u);
v_n_1431_ = lean_nat_sub(v_n_1410_, v_one_1430_);
v___x_1432_ = lean_nat_dec_eq(v_n_1431_, v_zero_1426_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
lean_inc_ref(v_type_1411_);
v___x_1433_ = l_Lean_Expr_cleanupAnnotations(v_type_1411_);
v___x_1434_ = l_Lean_Expr_isApp(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v___x_1433_);
lean_dec(v_n_1431_);
v___y_1418_ = v_a_1412_;
v___y_1419_ = v_a_1413_;
v___y_1420_ = v_a_1414_;
v___y_1421_ = v_a_1415_;
goto v___jp_1417_;
}
else
{
lean_object* v_arg_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_arg_1435_ = lean_ctor_get(v___x_1433_, 1);
lean_inc_ref(v_arg_1435_);
v___x_1436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1433_);
v___x_1437_ = l_Lean_Expr_isApp(v___x_1436_);
if (v___x_1437_ == 0)
{
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_arg_1435_);
lean_dec(v_n_1431_);
v___y_1418_ = v_a_1412_;
v___y_1419_ = v_a_1413_;
v___y_1420_ = v_a_1414_;
v___y_1421_ = v_a_1415_;
goto v___jp_1417_;
}
else
{
lean_object* v_arg_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_arg_1438_ = lean_ctor_get(v___x_1436_, 1);
lean_inc_ref(v_arg_1438_);
v___x_1439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1436_);
v___x_1440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1441_ = l_Lean_Expr_isConstOf(v___x_1439_, v___x_1440_);
lean_dec_ref(v___x_1439_);
if (v___x_1441_ == 0)
{
lean_dec_ref(v_arg_1438_);
lean_dec_ref(v_arg_1435_);
lean_dec(v_n_1431_);
v___y_1418_ = v_a_1412_;
v___y_1419_ = v_a_1413_;
v___y_1420_ = v_a_1414_;
v___y_1421_ = v_a_1415_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1442_; 
lean_dec_ref(v_type_1411_);
v___x_1442_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1431_, v_arg_1435_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
lean_dec(v_n_1431_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1451_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_arg_1438_);
lean_ctor_set(v___x_1447_, 1, v_a_1443_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1447_);
v___x_1449_ = v___x_1445_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
else
{
lean_dec_ref(v_arg_1438_);
return v___x_1442_;
}
}
}
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec(v_n_1431_);
v___x_1452_ = lean_box(0);
v___x_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_type_1411_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
}
v___jp_1417_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1422_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1);
v___x_1423_ = l_Lean_MessageData_ofExpr(v_type_1411_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1424_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object* v_n_1455_, lean_object* v_type_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1455_, v_type_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_n_1455_);
return v_res_1462_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0(void){
_start:
{
lean_object* v___x_1463_; lean_object* v_dummy_1464_; 
v___x_1463_ = lean_box(0);
v_dummy_1464_ = l_Lean_Expr_sort___override(v___x_1463_);
return v_dummy_1464_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1467_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1));
v___x_1468_ = lean_unsigned_to_nat(8u);
v___x_1469_ = lean_unsigned_to_nat(276u);
v___x_1470_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0));
v___x_1471_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1472_ = l_mkPanicMessageWithDecl(v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_, v___x_1467_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(lean_object* v_i_1481_, lean_object* v_fidx_1482_, lean_object* v_numFuncs_1483_, lean_object* v_arg_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_x_1485_) == 5)
{
lean_object* v_fn_1494_; lean_object* v_arg_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_fn_1494_ = lean_ctor_get(v_x_1485_, 0);
lean_inc_ref(v_fn_1494_);
v_arg_1495_ = lean_ctor_get(v_x_1485_, 1);
lean_inc_ref(v_arg_1495_);
lean_dec_ref_known(v_x_1485_, 2);
v___x_1496_ = lean_array_set(v_x_1486_, v_x_1487_, v_arg_1495_);
v___x_1497_ = lean_nat_sub(v_x_1487_, v___x_1493_);
lean_dec(v_x_1487_);
v_x_1485_ = v_fn_1494_;
v_x_1486_ = v___x_1496_;
v_x_1487_ = v___x_1497_;
goto _start;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
lean_dec(v_x_1487_);
v___x_1499_ = lean_array_get_size(v_x_1486_);
v___x_1500_ = lean_unsigned_to_nat(2u);
v___x_1501_ = lean_nat_dec_eq(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec_ref(v_x_1486_);
lean_dec_ref(v_x_1485_);
lean_dec_ref(v_arg_1484_);
v___x_1502_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2);
v___x_1503_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1502_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = l_Lean_instInhabitedExpr;
v___x_1505_ = lean_nat_dec_eq(v_i_1481_, v_fidx_1482_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_nat_add(v_i_1481_, v___x_1493_);
v___x_1507_ = lean_array_get(v___x_1504_, v_x_1486_, v___x_1493_);
lean_inc(v___x_1507_);
v___x_1508_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1483_, v_fidx_1482_, v_arg_1484_, v___x_1506_, v___x_1507_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___x_1506_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1522_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1522_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1522_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1513_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1514_ = l_Lean_Expr_constLevels_x21(v_x_1485_);
lean_dec_ref(v_x_1485_);
v___x_1515_ = l_Lean_mkConst(v___x_1513_, v___x_1514_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_array_get(v___x_1504_, v_x_1486_, v___x_1516_);
lean_dec_ref(v_x_1486_);
v___x_1518_ = l_Lean_mkApp3(v___x_1515_, v___x_1517_, v___x_1507_, v_a_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1518_);
v___x_1520_ = v___x_1511_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_dec(v___x_1507_);
lean_dec_ref(v_x_1486_);
lean_dec_ref(v_x_1485_);
return v___x_1508_;
}
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1523_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1524_ = l_Lean_Expr_constLevels_x21(v_x_1485_);
lean_dec_ref(v_x_1485_);
v___x_1525_ = l_Lean_mkConst(v___x_1523_, v___x_1524_);
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = lean_array_get(v___x_1504_, v_x_1486_, v___x_1526_);
v___x_1528_ = lean_array_get(v___x_1504_, v_x_1486_, v___x_1493_);
lean_dec_ref(v_x_1486_);
v___x_1529_ = l_Lean_mkApp3(v___x_1525_, v___x_1527_, v___x_1528_, v_arg_1484_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(lean_object* v_numFuncs_1531_, lean_object* v_fidx_1532_, lean_object* v_arg_1533_, lean_object* v_i_1534_, lean_object* v_type_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_sub(v_numFuncs_1531_, v___x_1541_);
v___x_1543_ = lean_nat_dec_le(v___x_1542_, v_i_1534_);
lean_dec(v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Meta_whnfD(v_type_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v_dummy_1546_; lean_object* v_nargs_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v_dummy_1546_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
v_nargs_1547_ = l_Lean_Expr_getAppNumArgs(v_a_1545_);
lean_inc(v_nargs_1547_);
v___x_1548_ = lean_mk_array(v_nargs_1547_, v_dummy_1546_);
v___x_1549_ = lean_nat_sub(v_nargs_1547_, v___x_1541_);
lean_dec(v_nargs_1547_);
v___x_1550_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1534_, v_fidx_1532_, v_numFuncs_1531_, v_arg_1533_, v_a_1545_, v___x_1548_, v___x_1549_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
return v___x_1550_;
}
else
{
lean_dec_ref(v_arg_1533_);
return v___x_1544_;
}
}
else
{
lean_object* v___x_1551_; 
lean_dec_ref(v_type_1535_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_arg_1533_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___boxed(lean_object* v_numFuncs_1552_, lean_object* v_fidx_1553_, lean_object* v_arg_1554_, lean_object* v_i_1555_, lean_object* v_type_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1552_, v_fidx_1553_, v_arg_1554_, v_i_1555_, v_type_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_i_1555_);
lean_dec(v_fidx_1553_);
lean_dec(v_numFuncs_1552_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___boxed(lean_object* v_i_1563_, lean_object* v_fidx_1564_, lean_object* v_numFuncs_1565_, lean_object* v_arg_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1563_, v_fidx_1564_, v_numFuncs_1565_, v_arg_1566_, v_x_1567_, v_x_1568_, v_x_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v_numFuncs_1565_);
lean_dec(v_fidx_1564_);
lean_dec(v_i_1563_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object* v_numFuncs_1576_, lean_object* v_domain_1577_, lean_object* v_fidx_1578_, lean_object* v_arg_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_unsigned_to_nat(0u);
v___x_1586_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1576_, v_fidx_1578_, v_arg_1579_, v___x_1585_, v_domain_1577_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object* v_numFuncs_1587_, lean_object* v_domain_1588_, lean_object* v_fidx_1589_, lean_object* v_arg_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v_numFuncs_1587_, v_domain_1588_, v_fidx_1589_, v_arg_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_fidx_1589_);
lean_dec(v_numFuncs_1587_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(lean_object* v_numFuncs_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1635_; 
v_fst_1599_ = lean_ctor_get(v_a_1598_, 0);
v_snd_1600_ = lean_ctor_get(v_a_1598_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_a_1598_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1602_ = v_a_1598_;
v_isShared_1603_ = v_isSharedCheck_1635_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_snd_1600_);
lean_inc(v_fst_1599_);
lean_dec(v_a_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1635_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_add(v_fst_1599_, v___x_1604_);
v___x_1606_ = lean_nat_dec_lt(v___x_1605_, v_numFuncs_1597_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1608_; 
lean_dec(v___x_1605_);
if (v_isShared_1603_ == 0)
{
v___x_1608_ = v___x_1602_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_fst_1599_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_snd_1600_);
v___x_1608_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1612_ = lean_unsigned_to_nat(3u);
v___x_1613_ = l_Lean_Expr_isAppOfArity(v_snd_1600_, v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
lean_dec(v___x_1605_);
v___x_1614_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1615_ = l_Lean_Expr_isAppOfArity(v_snd_1600_, v___x_1614_, v___x_1612_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
lean_del_object(v___x_1602_);
lean_dec(v_snd_1600_);
lean_dec(v_fst_1599_);
v___x_1616_ = lean_box(0);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1617_ = lean_unsigned_to_nat(2u);
v___x_1618_ = l_Lean_Expr_getAppNumArgs(v_snd_1600_);
v___x_1619_ = lean_nat_sub(v___x_1618_, v___x_1617_);
lean_dec(v___x_1618_);
v___x_1620_ = lean_nat_sub(v___x_1619_, v___x_1604_);
lean_dec(v___x_1619_);
v___x_1621_ = l_Lean_Expr_getRevArg_x21(v_snd_1600_, v___x_1620_);
lean_dec(v_snd_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v___x_1621_);
v___x_1623_ = v___x_1602_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_fst_1599_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
lean_dec(v_fst_1599_);
v___x_1626_ = lean_unsigned_to_nat(2u);
v___x_1627_ = l_Lean_Expr_getAppNumArgs(v_snd_1600_);
v___x_1628_ = lean_nat_sub(v___x_1627_, v___x_1626_);
lean_dec(v___x_1627_);
v___x_1629_ = lean_nat_sub(v___x_1628_, v___x_1604_);
lean_dec(v___x_1628_);
v___x_1630_ = l_Lean_Expr_getRevArg_x21(v_snd_1600_, v___x_1629_);
lean_dec(v_snd_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v___x_1630_);
lean_ctor_set(v___x_1602_, 0, v___x_1605_);
v___x_1632_ = v___x_1602_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
v_a_1598_ = v___x_1632_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg___boxed(lean_object* v_numFuncs_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1636_, v_a_1637_);
lean_dec(v_numFuncs_1636_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object* v_numFuncs_1639_, lean_object* v_expr_1640_){
_start:
{
lean_object* v_funidx_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_funidx_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_funidx_1641_);
lean_ctor_set(v___x_1642_, 1, v_expr_1640_);
v___x_1643_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1639_, v___x_1642_);
if (lean_obj_tag(v___x_1643_) == 0)
{
return v___x_1643_;
}
else
{
lean_object* v_val_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1660_; 
v_val_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1660_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_val_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1660_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v_fst_1648_; lean_object* v_snd_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1659_; 
v_fst_1648_ = lean_ctor_get(v_val_1644_, 0);
v_snd_1649_ = lean_ctor_get(v_val_1644_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_val_1644_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1651_ = v_val_1644_;
v_isShared_1652_ = v_isSharedCheck_1659_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_snd_1649_);
lean_inc(v_fst_1648_);
lean_dec(v_val_1644_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1659_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_fst_1648_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_snd_1649_);
v___x_1654_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1654_);
v___x_1656_ = v___x_1646_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(lean_object* v_numFuncs_1661_, lean_object* v_expr_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v_numFuncs_1661_, v_expr_1662_);
lean_dec(v_numFuncs_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(lean_object* v_numFuncs_1664_, lean_object* v_inst_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1664_, v_a_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(lean_object* v_numFuncs_1668_, lean_object* v_inst_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(v_numFuncs_1668_, v_inst_1669_, v_a_1670_);
lean_dec(v_numFuncs_1668_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object* v___x_1672_, lean_object* v___x_1673_, lean_object* v_types_1674_, lean_object* v_i_1675_, uint8_t v___x_1676_, uint8_t v___x_1677_, uint8_t v___x_1678_, lean_object* v_x_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_inc_ref(v_x_1679_);
v___x_1685_ = lean_array_push(v___x_1672_, v_x_1679_);
v___x_1686_ = lean_array_get_borrowed(v___x_1673_, v_types_1674_, v_i_1675_);
v___x_1687_ = l_Lean_Expr_bindingBody_x21(v___x_1686_);
v___x_1688_ = lean_expr_instantiate1(v___x_1687_, v_x_1679_);
lean_dec_ref(v_x_1679_);
lean_dec_ref(v___x_1687_);
v___x_1689_ = l_Lean_Meta_mkLambdaFVars(v___x_1685_, v___x_1688_, v___x_1676_, v___x_1677_, v___x_1676_, v___x_1677_, v___x_1678_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec_ref(v___x_1685_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object* v___x_1690_, lean_object* v___x_1691_, lean_object* v_types_1692_, lean_object* v_i_1693_, lean_object* v___x_1694_, lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v_x_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
uint8_t v___x_1665__boxed_1703_; uint8_t v___x_1666__boxed_1704_; uint8_t v___x_1667__boxed_1705_; lean_object* v_res_1706_; 
v___x_1665__boxed_1703_ = lean_unbox(v___x_1694_);
v___x_1666__boxed_1704_ = lean_unbox(v___x_1695_);
v___x_1667__boxed_1705_ = lean_unbox(v___x_1696_);
v_res_1706_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v___x_1690_, v___x_1691_, v_types_1692_, v_i_1693_, v___x_1665__boxed_1703_, v___x_1666__boxed_1704_, v___x_1667__boxed_1705_, v_x_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v_i_1693_);
lean_dec_ref(v_types_1692_);
lean_dec_ref(v___x_1691_);
return v_res_1706_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1));
v___x_1710_ = lean_unsigned_to_nat(6u);
v___x_1711_ = lean_unsigned_to_nat(318u);
v___x_1712_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0));
v___x_1713_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1714_ = l_mkPanicMessageWithDecl(v___x_1713_, v___x_1712_, v___x_1711_, v___x_1710_, v___x_1709_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object* v_i_1718_, lean_object* v___x_1719_, lean_object* v_types_1720_, lean_object* v_u_1721_, lean_object* v___x_1722_, lean_object* v___x_1723_, lean_object* v___x_1724_, lean_object* v___x_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_1725__boxed_1732_; uint8_t v___x_1726__boxed_1733_; uint8_t v___x_1727__boxed_1734_; lean_object* v_res_1735_; 
v___x_1725__boxed_1732_ = lean_unbox(v___x_1723_);
v___x_1726__boxed_1733_ = lean_unbox(v___x_1724_);
v___x_1727__boxed_1734_ = lean_unbox(v___x_1725_);
v_res_1735_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_i_1718_, v___x_1719_, v_types_1720_, v_u_1721_, v___x_1722_, v___x_1725__boxed_1732_, v___x_1726__boxed_1733_, v___x_1727__boxed_1734_, v_x_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___x_1719_);
lean_dec(v_i_1718_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object* v_types_1736_, lean_object* v_u_1737_, lean_object* v_x_1738_, lean_object* v_i_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1745_ = l_Lean_instInhabitedExpr;
v___x_1746_ = lean_array_get_size(v_types_1736_);
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_sub(v___x_1746_, v___x_1747_);
v___x_1749_ = lean_nat_dec_lt(v_i_1739_, v___x_1748_);
lean_dec(v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec(v_u_1737_);
v___x_1750_ = lean_array_get(v___x_1745_, v_types_1736_, v_i_1739_);
lean_dec(v_i_1739_);
lean_dec_ref(v_types_1736_);
v___x_1751_ = l_Lean_Expr_bindingBody_x21(v___x_1750_);
lean_dec(v___x_1750_);
v___x_1752_ = lean_expr_instantiate1(v___x_1751_, v_x_1738_);
lean_dec_ref(v_x_1738_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; 
lean_inc(v_a_1743_);
lean_inc_ref(v_a_1742_);
lean_inc(v_a_1741_);
lean_inc_ref(v_a_1740_);
lean_inc_ref(v_x_1738_);
v___x_1754_ = lean_infer_type(v_x_1738_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l_Lean_Meta_whnfD(v_a_1755_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1756_, 1);
v___x_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1759_ = lean_unsigned_to_nat(2u);
v___x_1760_ = l_Lean_Expr_isAppOfArity(v_a_1757_, v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v_a_1757_);
lean_dec(v_i_1739_);
lean_dec_ref(v_x_1738_);
lean_dec(v_u_1737_);
lean_dec_ref(v_types_1736_);
v___x_1761_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
v___x_1762_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1761_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1762_;
}
else
{
lean_object* v_dummy_1763_; lean_object* v_nargs_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___f_1787_; lean_object* v___x_1788_; 
v_dummy_1763_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
v_nargs_1764_ = l_Lean_Expr_getAppNumArgs(v_a_1757_);
lean_inc(v_nargs_1764_);
v___x_1765_ = lean_mk_array(v_nargs_1764_, v_dummy_1763_);
v___x_1766_ = lean_nat_sub(v_nargs_1764_, v___x_1747_);
lean_dec(v_nargs_1764_);
lean_inc(v_a_1757_);
v___x_1767_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1757_, v___x_1765_, v___x_1766_);
v___x_1768_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
lean_inc_n(v_u_1737_, 2);
v___x_1769_ = l_Lean_Level_succ___override(v_u_1737_);
v___x_1770_ = l_Lean_Expr_getAppFn(v_a_1757_);
lean_dec(v_a_1757_);
v___x_1771_ = l_Lean_Expr_constLevels_x21(v___x_1770_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1769_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_mkConst(v___x_1768_, v___x_1772_);
v___x_1774_ = l_Lean_mkAppN(v___x_1773_, v___x_1767_);
v___x_1775_ = lean_mk_empty_array_with_capacity(v___x_1747_);
lean_inc_ref(v_x_1738_);
lean_inc_ref_n(v___x_1775_, 2);
v___x_1776_ = lean_array_push(v___x_1775_, v_x_1738_);
v___x_1777_ = l_Lean_mkSort(v_u_1737_);
v___x_1778_ = 0;
v___x_1779_ = 1;
v___x_1780_ = lean_box(v___x_1778_);
v___x_1781_ = lean_box(v___x_1749_);
v___x_1782_ = lean_box(v___x_1779_);
lean_inc(v_i_1739_);
lean_inc_ref(v_types_1736_);
v___f_1783_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1783_, 0, v___x_1775_);
lean_closure_set(v___f_1783_, 1, v___x_1745_);
lean_closure_set(v___f_1783_, 2, v_types_1736_);
lean_closure_set(v___f_1783_, 3, v_i_1739_);
lean_closure_set(v___f_1783_, 4, v___x_1780_);
lean_closure_set(v___f_1783_, 5, v___x_1781_);
lean_closure_set(v___f_1783_, 6, v___x_1782_);
v___x_1784_ = lean_box(v___x_1778_);
v___x_1785_ = lean_box(v___x_1749_);
v___x_1786_ = lean_box(v___x_1779_);
v___f_1787_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1787_, 0, v_i_1739_);
lean_closure_set(v___f_1787_, 1, v___x_1747_);
lean_closure_set(v___f_1787_, 2, v_types_1736_);
lean_closure_set(v___f_1787_, 3, v_u_1737_);
lean_closure_set(v___f_1787_, 4, v___x_1775_);
lean_closure_set(v___f_1787_, 5, v___x_1784_);
lean_closure_set(v___f_1787_, 6, v___x_1785_);
lean_closure_set(v___f_1787_, 7, v___x_1786_);
v___x_1788_ = l_Lean_Meta_mkLambdaFVars(v___x_1776_, v___x_1777_, v___x_1778_, v___x_1749_, v___x_1778_, v___x_1749_, v___x_1779_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
lean_dec_ref(v___x_1776_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = l_Lean_Expr_app___override(v___x_1774_, v_a_1789_);
v___x_1791_ = l_Lean_Expr_app___override(v___x_1790_, v_x_1738_);
v___x_1792_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_1793_ = l_Lean_Core_mkFreshUserName(v___x_1792_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_array_get_borrowed(v___x_1745_, v___x_1767_, v___x_1795_);
lean_inc(v___x_1796_);
v___x_1797_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1794_, v___x_1796_, v___f_1783_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v___x_1799_ = l_Lean_Core_mkFreshUserName(v___x_1792_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = lean_array_get(v___x_1745_, v___x_1767_, v___x_1747_);
lean_dec_ref(v___x_1767_);
v___x_1802_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1800_, v___x_1801_, v___f_1787_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1811_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1811_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1807_ = l_Lean_mkAppB(v___x_1791_, v_a_1798_, v_a_1803_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1807_);
v___x_1809_ = v___x_1805_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
else
{
lean_dec(v_a_1798_);
lean_dec_ref(v___x_1791_);
return v___x_1802_;
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_a_1798_);
lean_dec_ref(v___x_1791_);
lean_dec_ref(v___f_1787_);
lean_dec_ref(v___x_1767_);
v_a_1812_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1799_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1799_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_dec_ref(v___x_1791_);
lean_dec_ref(v___f_1787_);
lean_dec_ref(v___x_1767_);
return v___x_1797_;
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec_ref(v___x_1791_);
lean_dec_ref(v___f_1787_);
lean_dec_ref(v___f_1783_);
lean_dec_ref(v___x_1767_);
v_a_1820_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1793_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1793_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_dec_ref(v___f_1787_);
lean_dec_ref(v___f_1783_);
lean_dec_ref(v___x_1774_);
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_x_1738_);
return v___x_1788_;
}
}
}
else
{
lean_dec(v_i_1739_);
lean_dec_ref(v_x_1738_);
lean_dec(v_u_1737_);
lean_dec_ref(v_types_1736_);
return v___x_1756_;
}
}
else
{
lean_dec(v_i_1739_);
lean_dec_ref(v_x_1738_);
lean_dec(v_u_1737_);
lean_dec_ref(v_types_1736_);
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object* v_i_1828_, lean_object* v___x_1829_, lean_object* v_types_1830_, lean_object* v_u_1831_, lean_object* v___x_1832_, uint8_t v___x_1833_, uint8_t v___x_1834_, uint8_t v___x_1835_, lean_object* v_x_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_nat_add(v_i_1828_, v___x_1829_);
lean_inc_ref(v_x_1836_);
v___x_1843_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1830_, v_u_1831_, v_x_1836_, v___x_1842_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = lean_array_push(v___x_1832_, v_x_1836_);
v___x_1846_ = l_Lean_Meta_mkLambdaFVars(v___x_1845_, v_a_1844_, v___x_1833_, v___x_1834_, v___x_1833_, v___x_1834_, v___x_1835_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec_ref(v___x_1845_);
return v___x_1846_;
}
else
{
lean_dec_ref(v_x_1836_);
lean_dec_ref(v___x_1832_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object* v_types_1847_, lean_object* v_u_1848_, lean_object* v_x_1849_, lean_object* v_i_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1847_, v_u_1848_, v_x_1849_, v_i_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object* v_x_1857_, lean_object* v_body_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_Meta_getLevel(v_body_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object* v_x_1865_, lean_object* v_body_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1865_, v_body_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v_x_1865_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object* v_types_1874_, lean_object* v_x_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v___f_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; 
v___f_1881_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0));
v___x_1882_ = l_Lean_instInhabitedExpr;
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_array_get_borrowed(v___x_1882_, v_types_1874_, v___x_1883_);
v___x_1885_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1886_ = 0;
lean_inc(v___x_1884_);
v___x_1887_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_1884_, v___x_1885_, v___f_1881_, v___x_1886_, v___x_1886_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1874_, v_a_1888_, v_x_1875_, v___x_1883_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
return v___x_1889_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_types_1874_);
v_a_1890_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1887_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1887_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object* v_types_1898_, lean_object* v_x_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1898_, v_x_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object* v_a_1906_, lean_object* v___x_1907_, uint8_t v___x_1908_, lean_object* v_x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
lean_inc_ref(v_x_1909_);
v___x_1915_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_a_1906_, v_x_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = lean_mk_empty_array_with_capacity(v___x_1907_);
v___x_1918_ = lean_array_push(v___x_1917_, v_x_1909_);
v___x_1919_ = 1;
v___x_1920_ = 1;
v___x_1921_ = l_Lean_Meta_mkForallFVars(v___x_1918_, v_a_1916_, v___x_1908_, v___x_1919_, v___x_1919_, v___x_1920_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec_ref(v___x_1918_);
return v___x_1921_;
}
else
{
lean_dec_ref(v_x_1909_);
return v___x_1915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object* v_a_1922_, lean_object* v___x_1923_, lean_object* v___x_1924_, lean_object* v_x_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
uint8_t v___x_1823__boxed_1931_; lean_object* v_res_1932_; 
v___x_1823__boxed_1931_ = lean_unbox(v___x_1924_);
v_res_1932_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1922_, v___x_1923_, v___x_1823__boxed_1931_, v_x_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___x_1923_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t v_sz_1933_, size_t v_i_1934_, lean_object* v_bs_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1934_, v_sz_1933_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_bs_1935_);
return v___x_1942_;
}
else
{
lean_object* v_v_1943_; lean_object* v___x_1944_; lean_object* v_bs_x27_1945_; lean_object* v___x_1946_; 
v_v_1943_ = lean_array_uget(v_bs_1935_, v_i_1934_);
v___x_1944_ = lean_unsigned_to_nat(0u);
v_bs_x27_1945_ = lean_array_uset(v_bs_1935_, v_i_1934_, v___x_1944_);
v___x_1946_ = l_Lean_Meta_whnfForall(v_v_1943_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_add(v_i_1934_, v___x_1948_);
v___x_1950_ = lean_array_uset(v_bs_x27_1945_, v_i_1934_, v_a_1947_);
v_i_1934_ = v___x_1949_;
v_bs_1935_ = v___x_1950_;
goto _start;
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_bs_x27_1945_);
v_a_1952_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1946_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1946_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object* v_sz_1960_, lean_object* v_i_1961_, lean_object* v_bs_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
size_t v_sz_boxed_1968_; size_t v_i_boxed_1969_; lean_object* v_res_1970_; 
v_sz_boxed_1968_ = lean_unbox_usize(v_sz_1960_);
lean_dec(v_sz_1960_);
v_i_boxed_1969_ = lean_unbox_usize(v_i_1961_);
lean_dec(v_i_1961_);
v_res_1970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_1968_, v_i_boxed_1969_, v_bs_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1970_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0));
v___x_1973_ = l_Lean_stringToMessageData(v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object* v_as_1974_, size_t v_i_1975_, size_t v_stop_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_a_1984_; uint8_t v___x_1988_; 
v___x_1988_ = lean_usize_dec_eq(v_i_1975_, v_stop_1976_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = lean_array_uget_borrowed(v_as_1974_, v_i_1975_);
v___x_1990_ = l_Lean_Expr_isForall(v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
lean_inc(v___x_1989_);
v___x_1992_ = l_Lean_MessageData_ofExpr(v___x_1989_);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1993_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
v_a_1984_ = v_a_1995_;
goto v___jp_1983_;
}
else
{
return v___x_1994_;
}
}
else
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_box(0);
v_a_1984_ = v___x_1996_;
goto v___jp_1983_;
}
}
else
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_b_1977_);
return v___x_1997_;
}
v___jp_1983_:
{
size_t v___x_1985_; size_t v___x_1986_; 
v___x_1985_ = ((size_t)1ULL);
v___x_1986_ = lean_usize_add(v_i_1975_, v___x_1985_);
v_i_1975_ = v___x_1986_;
v_b_1977_ = v_a_1984_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object* v_as_1998_, lean_object* v_i_1999_, lean_object* v_stop_2000_, lean_object* v_b_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
size_t v_i_boxed_2007_; size_t v_stop_boxed_2008_; lean_object* v_res_2009_; 
v_i_boxed_2007_ = lean_unbox_usize(v_i_1999_);
lean_dec(v_i_1999_);
v_stop_boxed_2008_ = lean_unbox_usize(v_stop_2000_);
lean_dec(v_stop_2000_);
v_res_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_1998_, v_i_boxed_2007_, v_stop_boxed_2008_, v_b_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec_ref(v_as_1998_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_bs_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
if (v___x_2013_ == 0)
{
return v_bs_2012_;
}
else
{
lean_object* v_v_2014_; lean_object* v___x_2015_; lean_object* v_bs_x27_2016_; lean_object* v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v_v_2014_ = lean_array_uget(v_bs_2012_, v_i_2011_);
v___x_2015_ = lean_unsigned_to_nat(0u);
v_bs_x27_2016_ = lean_array_uset(v_bs_2012_, v_i_2011_, v___x_2015_);
v___x_2017_ = l_Lean_Expr_bindingDomain_x21(v_v_2014_);
lean_dec(v_v_2014_);
v___x_2018_ = ((size_t)1ULL);
v___x_2019_ = lean_usize_add(v_i_2011_, v___x_2018_);
v___x_2020_ = lean_array_uset(v_bs_x27_2016_, v_i_2011_, v___x_2017_);
v_i_2011_ = v___x_2019_;
v_bs_2012_ = v___x_2020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object* v_sz_2022_, lean_object* v_i_2023_, lean_object* v_bs_2024_){
_start:
{
size_t v_sz_boxed_2025_; size_t v_i_boxed_2026_; lean_object* v_res_2027_; 
v_sz_boxed_2025_ = lean_unbox_usize(v_sz_2022_);
lean_dec(v_sz_2022_);
v_i_boxed_2026_ = lean_unbox_usize(v_i_2023_);
lean_dec(v_i_2023_);
v_res_2027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_2025_, v_i_boxed_2026_, v_bs_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object* v_types_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2034_ = lean_array_get_size(v_types_2028_);
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2036_ = lean_nat_dec_eq(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
size_t v_sz_2037_; size_t v___x_2038_; lean_object* v___x_2039_; 
v_sz_2037_ = lean_array_size(v_types_2028_);
v___x_2038_ = ((size_t)0ULL);
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2037_, v___x_2038_, v_types_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; lean_object* v___f_2042_; lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc_n(v_a_2040_, 2);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = lean_box(v___x_2036_);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2042_, 0, v_a_2040_);
lean_closure_set(v___f_2042_, 1, v___x_2035_);
lean_closure_set(v___f_2042_, 2, v___x_2041_);
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = lean_array_get_size(v_a_2040_);
v___x_2062_ = lean_nat_dec_lt(v___x_2060_, v___x_2061_);
if (v___x_2062_ == 0)
{
goto v___jp_2043_;
}
else
{
lean_object* v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_usize_of_nat(v___x_2061_);
v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2040_, v___x_2038_, v___x_2064_, v___x_2063_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_dec_ref_known(v___x_2065_, 1);
goto v___jp_2043_;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v___f_2042_);
lean_dec(v_a_2040_);
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
v___jp_2043_:
{
size_t v_sz_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_sz_2044_ = lean_array_size(v_a_2040_);
v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_2044_, v___x_2038_, v_a_2040_);
v___x_2046_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2045_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2049_ = l_Lean_Core_mkFreshUserName(v___x_2048_, v_a_2031_, v_a_2032_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___x_2051_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2050_, v_a_2047_, v___f_2042_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
return v___x_2051_;
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_a_2047_);
lean_dec_ref(v___f_2042_);
v_a_2052_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2049_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2049_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_dec_ref(v___f_2042_);
return v___x_2046_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_a_2074_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2039_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2039_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2082_ = l_Lean_instInhabitedExpr;
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = lean_array_get(v___x_2082_, v_types_2028_, v___x_2083_);
lean_dec_ref(v_types_2028_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object* v_types_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
return v_res_2092_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0));
v___x_2095_ = l_Lean_stringToMessageData(v___x_2094_);
return v___x_2095_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2));
v___x_2098_ = l_Lean_stringToMessageData(v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object* v___x_2099_, lean_object* v_as_2100_, size_t v_i_2101_, size_t v_stop_2102_, lean_object* v_b_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_a_2110_; uint8_t v___x_2114_; 
v___x_2114_ = lean_usize_dec_eq(v_i_2101_, v_stop_2102_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_array_uget_borrowed(v_as_2100_, v_i_2101_);
lean_inc_ref(v___x_2099_);
lean_inc(v___x_2115_);
v___x_2116_ = l_Lean_Meta_isExprDefEq(v___x_2115_, v___x_2099_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; uint8_t v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = lean_unbox(v_a_2117_);
lean_dec(v_a_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
lean_inc(v___x_2115_);
v___x_2120_ = l_Lean_MessageData_ofExpr(v___x_2115_);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2121_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
lean_inc_ref(v___x_2099_);
v___x_2124_ = l_Lean_MessageData_ofExpr(v___x_2099_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2125_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v_a_2110_ = v_a_2127_;
goto v___jp_2109_;
}
else
{
lean_dec_ref(v___x_2099_);
return v___x_2126_;
}
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_box(0);
v_a_2110_ = v___x_2128_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v___x_2099_);
v_a_2129_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2116_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2116_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref(v___x_2099_);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v_b_2103_);
return v___x_2137_;
}
v___jp_2109_:
{
size_t v___x_2111_; size_t v___x_2112_; 
v___x_2111_ = ((size_t)1ULL);
v___x_2112_ = lean_usize_add(v_i_2101_, v___x_2111_);
v_i_2101_ = v___x_2112_;
v_b_2103_ = v_a_2110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object* v___x_2138_, lean_object* v_as_2139_, lean_object* v_i_2140_, lean_object* v_stop_2141_, lean_object* v_b_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
size_t v_i_boxed_2148_; size_t v_stop_boxed_2149_; lean_object* v_res_2150_; 
v_i_boxed_2148_ = lean_unbox_usize(v_i_2140_);
lean_dec(v_i_2140_);
v_stop_boxed_2149_ = lean_unbox_usize(v_stop_2141_);
lean_dec(v_stop_2141_);
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2138_, v_as_2139_, v_i_boxed_2148_, v_stop_boxed_2149_, v_b_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v_as_2139_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t v_sz_2151_, size_t v_i_2152_, lean_object* v_bs_2153_){
_start:
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_usize_dec_lt(v_i_2152_, v_sz_2151_);
if (v___x_2154_ == 0)
{
return v_bs_2153_;
}
else
{
lean_object* v_v_2155_; lean_object* v___x_2156_; lean_object* v_bs_x27_2157_; lean_object* v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; lean_object* v___x_2161_; 
v_v_2155_ = lean_array_uget(v_bs_2153_, v_i_2152_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v_bs_x27_2157_ = lean_array_uset(v_bs_2153_, v_i_2152_, v___x_2156_);
v___x_2158_ = l_Lean_Expr_bindingBody_x21(v_v_2155_);
lean_dec(v_v_2155_);
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2152_, v___x_2159_);
v___x_2161_ = lean_array_uset(v_bs_x27_2157_, v_i_2152_, v___x_2158_);
v_i_2152_ = v___x_2160_;
v_bs_2153_ = v___x_2161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object* v_sz_2163_, lean_object* v_i_2164_, lean_object* v_bs_2165_){
_start:
{
size_t v_sz_boxed_2166_; size_t v_i_boxed_2167_; lean_object* v_res_2168_; 
v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2167_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_2166_, v_i_boxed_2167_, v_bs_2165_);
return v_res_2168_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0));
v___x_2171_ = l_Lean_stringToMessageData(v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object* v_as_2172_, size_t v_i_2173_, size_t v_stop_2174_, lean_object* v_b_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_a_2182_; uint8_t v___x_2186_; 
v___x_2186_ = lean_usize_dec_eq(v_i_2173_, v_stop_2174_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2187_ = lean_array_uget_borrowed(v_as_2172_, v_i_2173_);
v___x_2188_ = l_Lean_Expr_isArrow(v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2189_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
lean_inc(v___x_2187_);
v___x_2190_ = l_Lean_MessageData_ofExpr(v___x_2187_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2191_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v_a_2182_ = v_a_2193_;
goto v___jp_2181_;
}
else
{
return v___x_2192_;
}
}
else
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_box(0);
v_a_2182_ = v___x_2194_;
goto v___jp_2181_;
}
}
else
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v_b_2175_);
return v___x_2195_;
}
v___jp_2181_:
{
size_t v___x_2183_; size_t v___x_2184_; 
v___x_2183_ = ((size_t)1ULL);
v___x_2184_ = lean_usize_add(v_i_2173_, v___x_2183_);
v_i_2173_ = v___x_2184_;
v_b_2175_ = v_a_2182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object* v_as_2196_, lean_object* v_i_2197_, lean_object* v_stop_2198_, lean_object* v_b_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
size_t v_i_boxed_2205_; size_t v_stop_boxed_2206_; lean_object* v_res_2207_; 
v_i_boxed_2205_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_stop_boxed_2206_ = lean_unbox_usize(v_stop_2198_);
lean_dec(v_stop_2198_);
v_res_2207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2196_, v_i_boxed_2205_, v_stop_boxed_2206_, v_b_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_as_2196_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object* v_types_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v___x_2214_; size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = l_Lean_instInhabitedExpr;
v_sz_2215_ = lean_array_size(v_types_2208_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2215_, v___x_2216_, v_types_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___y_2221_; size_t v___y_2222_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2249_ = lean_array_get_size(v_a_2218_);
v___x_2250_ = lean_nat_dec_lt(v___x_2219_, v___x_2249_);
if (v___x_2250_ == 0)
{
goto v___jp_2228_;
}
else
{
lean_object* v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_usize_of_nat(v___x_2249_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2218_, v___x_2216_, v___x_2252_, v___x_2251_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_dec_ref_known(v___x_2253_, 1);
goto v___jp_2228_;
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2218_);
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
v___jp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_array_get(v___x_2214_, v___y_2221_, v___x_2219_);
lean_dec_ref(v___y_2221_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_2222_, v___x_2216_, v_a_2218_);
v___x_2225_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2224_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2227_ = l_Lean_mkArrow(v_a_2226_, v___x_2223_, v_a_2211_, v_a_2212_);
return v___x_2227_;
}
else
{
lean_dec(v___x_2223_);
return v___x_2225_;
}
}
v___jp_2228_:
{
size_t v_sz_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_sz_2229_ = lean_array_size(v_a_2218_);
lean_inc(v_a_2218_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2229_, v___x_2216_, v_a_2218_);
v___x_2231_ = lean_array_get_size(v___x_2230_);
v___x_2232_ = lean_unsigned_to_nat(1u);
v___x_2233_ = lean_nat_sub(v___x_2231_, v___x_2232_);
v___x_2234_ = lean_array_get_borrowed(v___x_2214_, v___x_2230_, v___x_2233_);
lean_dec(v___x_2233_);
lean_inc_ref(v___x_2230_);
v___x_2235_ = lean_array_pop(v___x_2230_);
v___x_2236_ = lean_array_get_size(v___x_2235_);
v___x_2237_ = lean_nat_dec_lt(v___x_2219_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_dec_ref(v___x_2235_);
v___y_2221_ = v___x_2230_;
v___y_2222_ = v_sz_2229_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2238_; size_t v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_box(0);
v___x_2239_ = lean_usize_of_nat(v___x_2236_);
lean_inc(v___x_2234_);
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2234_, v___x_2235_, v___x_2216_, v___x_2239_, v___x_2238_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec_ref(v___x_2235_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_dec_ref_known(v___x_2240_, 1);
v___y_2221_ = v___x_2230_;
v___y_2222_ = v_sz_2229_;
goto v___jp_2220_;
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v___x_2230_);
lean_dec(v_a_2218_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_a_2262_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2217_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2217_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object* v_types_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
return v_res_2276_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0));
v___x_2279_ = l_Lean_stringToMessageData(v___x_2278_);
return v___x_2279_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2));
v___x_2282_ = l_Lean_stringToMessageData(v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object* v___x_2283_, lean_object* v___x_2284_, lean_object* v_arg_2285_, lean_object* v_arg_2286_, lean_object* v___x_2287_, lean_object* v_a_2288_, lean_object* v_tail_2289_, lean_object* v___x_2290_, lean_object* v___x_2291_, lean_object* v___x_2292_, lean_object* v_y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v___x_2270__boxed_2299_; uint8_t v___x_2271__boxed_2300_; uint8_t v___x_2272__boxed_2301_; lean_object* v_res_2302_; 
v___x_2270__boxed_2299_ = lean_unbox(v___x_2290_);
v___x_2271__boxed_2300_ = lean_unbox(v___x_2291_);
v___x_2272__boxed_2301_ = lean_unbox(v___x_2292_);
v_res_2302_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v___x_2283_, v___x_2284_, v_arg_2285_, v_arg_2286_, v___x_2287_, v_a_2288_, v_tail_2289_, v___x_2270__boxed_2299_, v___x_2271__boxed_2300_, v___x_2272__boxed_2301_, v_y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object* v_x_2303_, lean_object* v_codomain_2304_, lean_object* v_alts_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
if (lean_obj_tag(v_alts_2305_) == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v_codomain_2304_);
lean_dec_ref(v_x_2303_);
v___x_2311_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
v___x_2312_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2311_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
return v___x_2312_;
}
else
{
lean_object* v_tail_2313_; 
v_tail_2313_ = lean_ctor_get(v_alts_2305_, 1);
if (lean_obj_tag(v_tail_2313_) == 0)
{
lean_object* v_head_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec_ref(v_codomain_2304_);
v_head_2314_ = lean_ctor_get(v_alts_2305_, 0);
lean_inc(v_head_2314_);
lean_dec_ref_known(v_alts_2305_, 2);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = lean_mk_empty_array_with_capacity(v___x_2315_);
v___x_2317_ = lean_array_push(v___x_2316_, v_x_2303_);
v___x_2318_ = l_Lean_Expr_beta(v_head_2314_, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
return v___x_2319_;
}
else
{
lean_object* v_head_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2405_; 
lean_inc(v_tail_2313_);
v_head_2320_ = lean_ctor_get(v_alts_2305_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_alts_2305_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v_alts_2305_, 1);
lean_dec(v_unused_2406_);
v___x_2322_ = v_alts_2305_;
v_isShared_2323_ = v_isSharedCheck_2405_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_head_2320_);
lean_dec(v_alts_2305_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2405_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; 
lean_inc(v_a_2309_);
lean_inc_ref(v_a_2308_);
lean_inc(v_a_2307_);
lean_inc_ref(v_a_2306_);
lean_inc_ref(v_x_2303_);
v___x_2324_ = lean_infer_type(v_x_2303_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___x_2335_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc_n(v_a_2325_, 2);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2335_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2325_, v_a_2307_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = l_Lean_Expr_cleanupAnnotations(v_a_2336_);
v___x_2338_ = l_Lean_Expr_isApp(v___x_2337_);
if (v___x_2338_ == 0)
{
lean_dec_ref(v___x_2337_);
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec(v_tail_2313_);
lean_dec_ref(v_codomain_2304_);
lean_dec_ref(v_x_2303_);
v___y_2327_ = v_a_2306_;
v___y_2328_ = v_a_2307_;
v___y_2329_ = v_a_2308_;
v___y_2330_ = v_a_2309_;
goto v___jp_2326_;
}
else
{
lean_object* v_arg_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v_arg_2339_ = lean_ctor_get(v___x_2337_, 1);
lean_inc_ref(v_arg_2339_);
v___x_2340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2337_);
v___x_2341_ = l_Lean_Expr_isApp(v___x_2340_);
if (v___x_2341_ == 0)
{
lean_dec_ref(v___x_2340_);
lean_dec_ref(v_arg_2339_);
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec(v_tail_2313_);
lean_dec_ref(v_codomain_2304_);
lean_dec_ref(v_x_2303_);
v___y_2327_ = v_a_2306_;
v___y_2328_ = v_a_2307_;
v___y_2329_ = v_a_2308_;
v___y_2330_ = v_a_2309_;
goto v___jp_2326_;
}
else
{
lean_object* v_arg_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; 
v_arg_2342_ = lean_ctor_get(v___x_2340_, 1);
lean_inc_ref(v_arg_2342_);
v___x_2343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2340_);
v___x_2344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0));
v___x_2345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_2346_ = l_Lean_Expr_isConstOf(v___x_2343_, v___x_2345_);
lean_dec_ref(v___x_2343_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_arg_2339_);
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec(v_tail_2313_);
lean_dec_ref(v_codomain_2304_);
lean_dec_ref(v_x_2303_);
v___y_2327_ = v_a_2306_;
v___y_2328_ = v_a_2307_;
v___y_2329_ = v_a_2308_;
v___y_2330_ = v_a_2309_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2347_; 
lean_inc_ref(v_codomain_2304_);
v___x_2347_ = l_Lean_Meta_getLevel(v_codomain_2304_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = l_Lean_Expr_getAppFn(v_a_2325_);
lean_dec(v_a_2325_);
v___x_2350_ = l_Lean_Expr_constLevels_x21(v___x_2349_);
lean_dec_ref(v___x_2349_);
v___x_2351_ = lean_unsigned_to_nat(1u);
v___x_2352_ = lean_mk_empty_array_with_capacity(v___x_2351_);
lean_inc_ref(v_x_2303_);
lean_inc_ref(v___x_2352_);
v___x_2353_ = lean_array_push(v___x_2352_, v_x_2303_);
v___x_2354_ = 0;
v___x_2355_ = 1;
v___x_2356_ = l_Lean_Meta_mkLambdaFVars(v___x_2353_, v_codomain_2304_, v___x_2354_, v___x_2346_, v___x_2354_, v___x_2346_, v___x_2355_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec_ref(v___x_2353_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2396_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2396_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2396_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v_alt_u2082_2362_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___f_2375_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; 
v___x_2372_ = lean_box(v___x_2354_);
v___x_2373_ = lean_box(v___x_2346_);
v___x_2374_ = lean_box(v___x_2355_);
lean_inc(v_tail_2313_);
lean_inc(v_a_2357_);
lean_inc_ref(v_arg_2339_);
lean_inc_ref(v_arg_2342_);
lean_inc(v___x_2350_);
v___f_2375_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2375_, 0, v___x_2344_);
lean_closure_set(v___f_2375_, 1, v___x_2350_);
lean_closure_set(v___f_2375_, 2, v_arg_2342_);
lean_closure_set(v___f_2375_, 3, v_arg_2339_);
lean_closure_set(v___f_2375_, 4, v___x_2352_);
lean_closure_set(v___f_2375_, 5, v_a_2357_);
lean_closure_set(v___f_2375_, 6, v_tail_2313_);
lean_closure_set(v___f_2375_, 7, v___x_2372_);
lean_closure_set(v___f_2375_, 8, v___x_2373_);
lean_closure_set(v___f_2375_, 9, v___x_2374_);
if (lean_obj_tag(v_tail_2313_) == 1)
{
lean_object* v_tail_2394_; 
v_tail_2394_ = lean_ctor_get(v_tail_2313_, 1);
if (lean_obj_tag(v_tail_2394_) == 0)
{
lean_object* v_head_2395_; 
lean_dec_ref(v___f_2375_);
v_head_2395_ = lean_ctor_get(v_tail_2313_, 0);
lean_inc(v_head_2395_);
lean_dec_ref_known(v_tail_2313_, 2);
v_alt_u2082_2362_ = v_head_2395_;
goto v___jp_2361_;
}
else
{
lean_dec_ref_known(v_tail_2313_, 2);
v___y_2377_ = v_a_2306_;
v___y_2378_ = v_a_2307_;
v___y_2379_ = v_a_2308_;
v___y_2380_ = v_a_2309_;
goto v___jp_2376_;
}
}
else
{
lean_dec(v_tail_2313_);
v___y_2377_ = v_a_2306_;
v___y_2378_ = v_a_2307_;
v___y_2379_ = v_a_2308_;
v___y_2380_ = v_a_2309_;
goto v___jp_2376_;
}
v___jp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v___x_2350_);
lean_ctor_set(v___x_2322_, 0, v_a_2348_);
v___x_2365_ = v___x_2322_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2348_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2350_);
v___x_2365_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2366_ = l_Lean_Expr_const___override(v___x_2363_, v___x_2365_);
v___x_2367_ = l_Lean_mkApp6(v___x_2366_, v_arg_2342_, v_arg_2339_, v_a_2357_, v_x_2303_, v_head_2320_, v_alt_u2082_2362_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2367_);
v___x_2369_ = v___x_2359_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
v___jp_2376_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_2382_ = l_Lean_Core_mkFreshUserName(v___x_2381_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
lean_inc_ref(v_arg_2339_);
v___x_2384_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2383_, v_arg_2339_, v___f_2375_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v_alt_u2082_2362_ = v_a_2385_;
goto v___jp_2361_;
}
else
{
lean_del_object(v___x_2359_);
lean_dec(v_a_2357_);
lean_dec(v___x_2350_);
lean_dec(v_a_2348_);
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_arg_2339_);
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec_ref(v_x_2303_);
return v___x_2384_;
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v___f_2375_);
lean_del_object(v___x_2359_);
lean_dec(v_a_2357_);
lean_dec(v___x_2350_);
lean_dec(v_a_2348_);
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_arg_2339_);
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec_ref(v_x_2303_);
v_a_2386_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2382_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2382_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2352_);
lean_dec(v___x_2350_);
lean_dec(v_a_2348_);
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_arg_2339_);
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec(v_tail_2313_);
lean_dec_ref(v_x_2303_);
return v___x_2356_;
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_arg_2339_);
lean_dec(v_a_2325_);
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec(v_tail_2313_);
lean_dec_ref(v_codomain_2304_);
lean_dec_ref(v_x_2303_);
v_a_2397_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2347_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2347_);
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
}
}
else
{
lean_dec(v_a_2325_);
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec(v_tail_2313_);
lean_dec_ref(v_codomain_2304_);
lean_dec_ref(v_x_2303_);
return v___x_2335_;
}
v___jp_2326_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2331_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
v___x_2332_ = l_Lean_MessageData_ofExpr(v_a_2325_);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2333_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
return v___x_2334_;
}
}
else
{
lean_del_object(v___x_2322_);
lean_dec(v_head_2320_);
lean_dec(v_tail_2313_);
lean_dec_ref(v_codomain_2304_);
lean_dec_ref(v_x_2303_);
return v___x_2324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object* v___x_2407_, lean_object* v___x_2408_, lean_object* v_arg_2409_, lean_object* v_arg_2410_, lean_object* v___x_2411_, lean_object* v_a_2412_, lean_object* v_tail_2413_, uint8_t v___x_2414_, uint8_t v___x_2415_, uint8_t v___x_2416_, lean_object* v_y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2423_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3));
v___x_2424_ = l_Lean_Name_mkStr2(v___x_2407_, v___x_2423_);
v___x_2425_ = l_Lean_Expr_const___override(v___x_2424_, v___x_2408_);
lean_inc_ref_n(v_y_2417_, 2);
v___x_2426_ = l_Lean_mkApp3(v___x_2425_, v_arg_2409_, v_arg_2410_, v_y_2417_);
lean_inc_ref(v___x_2411_);
v___x_2427_ = lean_array_push(v___x_2411_, v___x_2426_);
v___x_2428_ = l_Lean_Expr_beta(v_a_2412_, v___x_2427_);
v___x_2429_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_y_2417_, v___x_2428_, v_tail_2413_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = lean_array_push(v___x_2411_, v_y_2417_);
v___x_2432_ = l_Lean_Meta_mkLambdaFVars(v___x_2431_, v_a_2430_, v___x_2414_, v___x_2415_, v___x_2414_, v___x_2415_, v___x_2416_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec_ref(v___x_2431_);
return v___x_2432_;
}
else
{
lean_dec_ref(v_y_2417_);
lean_dec_ref(v___x_2411_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object* v_x_2433_, lean_object* v_codomain_2434_, lean_object* v_alts_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2433_, v_codomain_2434_, v_alts_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
return v_res_2441_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2443_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2444_ = lean_unsigned_to_nat(21u);
v___x_2445_ = lean_unsigned_to_nat(414u);
v___x_2446_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0));
v___x_2447_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2448_ = l_mkPanicMessageWithDecl(v___x_2447_, v___x_2446_, v___x_2445_, v___x_2444_, v___x_2443_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object* v___x_2449_, lean_object* v_es_2450_, lean_object* v_xs_2451_, lean_object* v_codomain_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = lean_array_get_size(v_xs_2451_);
v___x_2459_ = lean_nat_dec_eq(v___x_2458_, v___x_2449_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_dec_ref(v_codomain_2452_);
lean_dec_ref(v_es_2450_);
v___x_2460_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1);
v___x_2461_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2460_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = lean_array_fget_borrowed(v_xs_2451_, v___x_2462_);
v___x_2464_ = lean_array_to_list(v_es_2450_);
lean_inc(v___x_2463_);
v___x_2465_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2463_, v_codomain_2452_, v___x_2464_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_mk_empty_array_with_capacity(v___x_2449_);
lean_inc(v___x_2463_);
v___x_2468_ = lean_array_push(v___x_2467_, v___x_2463_);
v___x_2469_ = 0;
v___x_2470_ = 1;
v___x_2471_ = l_Lean_Meta_mkLambdaFVars(v___x_2468_, v_a_2466_, v___x_2469_, v___x_2459_, v___x_2469_, v___x_2459_, v___x_2470_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec_ref(v___x_2468_);
return v___x_2471_;
}
else
{
return v___x_2465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(lean_object* v___x_2472_, lean_object* v_es_2473_, lean_object* v_xs_2474_, lean_object* v_codomain_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(v___x_2472_, v_es_2473_, v_xs_2474_, v_codomain_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v_xs_2474_);
lean_dec(v___x_2472_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(lean_object* v_resultType_2482_, lean_object* v_es_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2489_ = lean_unsigned_to_nat(1u);
v___f_2490_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2490_, 0, v___x_2489_);
lean_closure_set(v___f_2490_, 1, v_es_2483_);
v___x_2491_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2492_ = 0;
v___x_2493_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_resultType_2482_, v___x_2491_, v___f_2490_, v___x_2492_, v___x_2492_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(lean_object* v_resultType_2494_, lean_object* v_es_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_2494_, v_es_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(size_t v_sz_2502_, size_t v_i_2503_, lean_object* v_bs_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v___x_2510_; 
v___x_2510_ = lean_usize_dec_lt(v_i_2503_, v_sz_2502_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_bs_2504_);
return v___x_2511_;
}
else
{
lean_object* v_v_2512_; lean_object* v___x_2513_; lean_object* v_bs_x27_2514_; lean_object* v___x_2515_; 
v_v_2512_ = lean_array_uget(v_bs_2504_, v_i_2503_);
v___x_2513_ = lean_unsigned_to_nat(0u);
v_bs_x27_2514_ = lean_array_uset(v_bs_2504_, v_i_2503_, v___x_2513_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
v___x_2515_ = lean_infer_type(v_v_2512_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2503_, v___x_2517_);
v___x_2519_ = lean_array_uset(v_bs_x27_2514_, v_i_2503_, v_a_2516_);
v_i_2503_ = v___x_2518_;
v_bs_2504_ = v___x_2519_;
goto _start;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v_bs_x27_2514_);
v_a_2521_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2515_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2515_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(lean_object* v_sz_2529_, lean_object* v_i_2530_, lean_object* v_bs_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
size_t v_sz_boxed_2537_; size_t v_i_boxed_2538_; lean_object* v_res_2539_; 
v_sz_boxed_2537_ = lean_unbox_usize(v_sz_2529_);
lean_dec(v_sz_2529_);
v_i_boxed_2538_ = lean_unbox_usize(v_i_2530_);
lean_dec(v_i_2530_);
v_res_2539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_boxed_2537_, v_i_boxed_2538_, v_bs_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry(lean_object* v_es_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
size_t v_sz_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
v_sz_2546_ = lean_array_size(v_es_2540_);
v___x_2547_ = ((size_t)0ULL);
lean_inc_ref(v_es_2540_);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2546_, v___x_2547_, v_es_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
v___x_2550_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2549_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2552_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_a_2551_, v_es_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
return v___x_2552_;
}
else
{
lean_dec_ref(v_es_2540_);
return v___x_2550_;
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v_es_2540_);
v_a_2553_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2548_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2548_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(lean_object* v_es_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_es_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
return v_res_2567_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2569_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2570_ = lean_unsigned_to_nat(21u);
v___x_2571_ = lean_unsigned_to_nat(434u);
v___x_2572_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0));
v___x_2573_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2574_ = l_mkPanicMessageWithDecl(v___x_2573_, v___x_2572_, v___x_2571_, v___x_2570_, v___x_2569_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(lean_object* v___x_2575_, lean_object* v_es_2576_, lean_object* v_xs_2577_, lean_object* v_codomain_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = lean_array_get_size(v_xs_2577_);
v___x_2585_ = lean_nat_dec_eq(v___x_2584_, v___x_2575_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec_ref(v_codomain_2578_);
lean_dec_ref(v_es_2576_);
v___x_2586_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1);
v___x_2587_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2586_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_array_fget_borrowed(v_xs_2577_, v___x_2588_);
v___x_2590_ = lean_array_to_list(v_es_2576_);
lean_inc(v___x_2589_);
v___x_2591_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2589_, v_codomain_2578_, v___x_2590_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; uint8_t v___x_2596_; lean_object* v___x_2597_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = lean_mk_empty_array_with_capacity(v___x_2575_);
lean_inc(v___x_2589_);
v___x_2594_ = lean_array_push(v___x_2593_, v___x_2589_);
v___x_2595_ = 0;
v___x_2596_ = 1;
v___x_2597_ = l_Lean_Meta_mkLambdaFVars(v___x_2594_, v_a_2592_, v___x_2595_, v___x_2585_, v___x_2595_, v___x_2585_, v___x_2596_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec_ref(v___x_2594_);
return v___x_2597_;
}
else
{
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object* v___x_2598_, lean_object* v_es_2599_, lean_object* v_xs_2600_, lean_object* v_codomain_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2598_, v_es_2599_, v_xs_2600_, v_codomain_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec_ref(v_xs_2600_);
lean_dec(v___x_2598_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object* v_es_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
size_t v_sz_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v_sz_2614_ = lean_array_size(v_es_2608_);
v___x_2615_ = ((size_t)0ULL);
lean_inc_ref(v_es_2608_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2614_, v___x_2615_, v_es_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_a_2617_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = lean_unsigned_to_nat(1u);
v___f_2621_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2621_, 0, v___x_2620_);
lean_closure_set(v___f_2621_, 1, v_es_2608_);
v___x_2622_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2623_ = 0;
v___x_2624_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_2619_, v___x_2622_, v___f_2621_, v___x_2623_, v___x_2623_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
return v___x_2624_;
}
else
{
lean_dec_ref(v_es_2608_);
return v___x_2618_;
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_es_2608_);
v_a_2625_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2616_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2616_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object* v_es_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object* v_a_2640_, lean_object* v_domain_2641_, lean_object* v___x_2642_, lean_object* v_type_2643_, uint8_t v___x_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = l_List_lengthTR___redArg(v_a_2640_);
lean_inc_ref(v_x_2645_);
v___x_2652_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2651_, v_domain_2641_, v___x_2642_, v_x_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___x_2651_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v___x_2654_ = lean_unsigned_to_nat(1u);
v___x_2655_ = lean_mk_empty_array_with_capacity(v___x_2654_);
lean_inc_ref(v___x_2655_);
v___x_2656_ = lean_array_push(v___x_2655_, v_a_2653_);
v___x_2657_ = l_Lean_Meta_instantiateForall(v_type_2643_, v___x_2656_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec_ref(v___x_2656_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = lean_array_push(v___x_2655_, v_x_2645_);
v___x_2660_ = 0;
v___x_2661_ = 1;
v___x_2662_ = l_Lean_Meta_mkForallFVars(v___x_2659_, v_a_2658_, v___x_2660_, v___x_2644_, v___x_2644_, v___x_2661_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec_ref(v___x_2659_);
return v___x_2662_;
}
else
{
lean_dec_ref(v___x_2655_);
lean_dec_ref(v_x_2645_);
return v___x_2657_;
}
}
else
{
lean_dec_ref(v_x_2645_);
lean_dec_ref(v_type_2643_);
return v___x_2652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object* v_a_2663_, lean_object* v_domain_2664_, lean_object* v___x_2665_, lean_object* v_type_2666_, lean_object* v___x_2667_, lean_object* v_x_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v___x_791__boxed_2674_; lean_object* v_res_2675_; 
v___x_791__boxed_2674_ = lean_unbox(v___x_2667_);
v_res_2675_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2663_, v_domain_2664_, v___x_2665_, v_type_2666_, v___x_791__boxed_2674_, v_x_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___x_2665_);
lean_dec(v_a_2663_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object* v_a_2676_, lean_object* v_domain_2677_, lean_object* v_type_2678_, size_t v_sz_2679_, size_t v_i_2680_, lean_object* v_bs_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = lean_usize_dec_lt(v_i_2680_, v_sz_2679_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec_ref(v_type_2678_);
lean_dec_ref(v_domain_2677_);
lean_dec(v_a_2676_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_bs_2681_);
return v___x_2688_;
}
else
{
lean_object* v_v_2689_; lean_object* v___x_2690_; lean_object* v_bs_x27_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___f_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_v_2689_ = lean_array_uget(v_bs_2681_, v_i_2680_);
v___x_2690_ = lean_unsigned_to_nat(0u);
v_bs_x27_2691_ = lean_array_uset(v_bs_2681_, v_i_2680_, v___x_2690_);
v___x_2692_ = lean_usize_to_nat(v_i_2680_);
v___x_2693_ = lean_box(v___x_2687_);
lean_inc_ref(v_type_2678_);
lean_inc_ref(v_domain_2677_);
lean_inc(v_a_2676_);
v___f_2694_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2694_, 0, v_a_2676_);
lean_closure_set(v___f_2694_, 1, v_domain_2677_);
lean_closure_set(v___f_2694_, 2, v___x_2692_);
lean_closure_set(v___f_2694_, 3, v_type_2678_);
lean_closure_set(v___f_2694_, 4, v___x_2693_);
v___x_2695_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2696_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_2695_, v_v_2689_, v___f_2694_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; size_t v___x_2698_; size_t v___x_2699_; lean_object* v___x_2700_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2696_, 1);
v___x_2698_ = ((size_t)1ULL);
v___x_2699_ = lean_usize_add(v_i_2680_, v___x_2698_);
v___x_2700_ = lean_array_uset(v_bs_x27_2691_, v_i_2680_, v_a_2697_);
v_i_2680_ = v___x_2699_;
v_bs_2681_ = v___x_2700_;
goto _start;
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v_bs_x27_2691_);
lean_dec_ref(v_type_2678_);
lean_dec_ref(v_domain_2677_);
lean_dec(v_a_2676_);
v_a_2702_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2696_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2696_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object* v_a_2710_, lean_object* v_domain_2711_, lean_object* v_type_2712_, lean_object* v_sz_2713_, lean_object* v_i_2714_, lean_object* v_bs_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
size_t v_sz_boxed_2721_; size_t v_i_boxed_2722_; lean_object* v_res_2723_; 
v_sz_boxed_2721_ = lean_unbox_usize(v_sz_2713_);
lean_dec(v_sz_2713_);
v_i_boxed_2722_ = lean_unbox_usize(v_i_2714_);
lean_dec(v_i_2714_);
v_res_2723_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2710_, v_domain_2711_, v_type_2712_, v_sz_boxed_2721_, v_i_boxed_2722_, v_bs_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object* v_n_2724_, lean_object* v_type_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; uint8_t v___x_2751_; 
v___x_2751_ = l_Lean_Expr_isForall(v_type_2725_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v___x_2752_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_2753_ = l_Lean_MessageData_ofExpr(v_type_2725_);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2754_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
else
{
v___y_2732_ = v_a_2726_;
v___y_2733_ = v_a_2727_;
v___y_2734_ = v_a_2728_;
v___y_2735_ = v_a_2729_;
goto v___jp_2731_;
}
v___jp_2731_:
{
lean_object* v_domain_2736_; lean_object* v___x_2737_; 
v_domain_2736_ = l_Lean_Expr_bindingDomain_x21(v_type_2725_);
lean_inc_ref(v_domain_2736_);
v___x_2737_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_2724_, v_domain_2736_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2739_; size_t v_sz_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc_n(v_a_2738_, 2);
lean_dec_ref_known(v___x_2737_, 1);
v___x_2739_ = lean_array_mk(v_a_2738_);
v_sz_2740_ = lean_array_size(v___x_2739_);
v___x_2741_ = ((size_t)0ULL);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2738_, v_domain_2736_, v_type_2725_, v_sz_2740_, v___x_2741_, v___x_2739_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
return v___x_2742_;
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_domain_2736_);
lean_dec_ref(v_type_2725_);
v_a_2743_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2737_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2737_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object* v_n_2764_, lean_object* v_type_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2764_, v_type_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_n_2764_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object* v_a_2772_, lean_object* v_domain_2773_, lean_object* v_type_2774_, lean_object* v_as_2775_, size_t v_sz_2776_, size_t v_i_2777_, lean_object* v_bs_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2772_, v_domain_2773_, v_type_2774_, v_sz_2776_, v_i_2777_, v_bs_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object* v_a_2785_, lean_object* v_domain_2786_, lean_object* v_type_2787_, lean_object* v_as_2788_, lean_object* v_sz_2789_, lean_object* v_i_2790_, lean_object* v_bs_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
size_t v_sz_boxed_2797_; size_t v_i_boxed_2798_; lean_object* v_res_2799_; 
v_sz_boxed_2797_ = lean_unbox_usize(v_sz_2789_);
lean_dec(v_sz_2789_);
v_i_boxed_2798_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_res_2799_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2785_, v_domain_2786_, v_type_2787_, v_as_2788_, v_sz_boxed_2797_, v_i_boxed_2798_, v_bs_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_as_2788_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object* v_argsPacker_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_array_get_size(v_argsPacker_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object* v_argsPacker_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_2802_);
lean_dec_ref(v_argsPacker_2802_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t v_sz_2804_, size_t v_i_2805_, lean_object* v_bs_2806_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_usize_dec_lt(v_i_2805_, v_sz_2804_);
if (v___x_2807_ == 0)
{
return v_bs_2806_;
}
else
{
lean_object* v_v_2808_; lean_object* v___x_2809_; lean_object* v_bs_x27_2810_; lean_object* v___x_2811_; size_t v___x_2812_; size_t v___x_2813_; lean_object* v___x_2814_; 
v_v_2808_ = lean_array_uget(v_bs_2806_, v_i_2805_);
v___x_2809_ = lean_unsigned_to_nat(0u);
v_bs_x27_2810_ = lean_array_uset(v_bs_2806_, v_i_2805_, v___x_2809_);
v___x_2811_ = lean_array_get_size(v_v_2808_);
lean_dec(v_v_2808_);
v___x_2812_ = ((size_t)1ULL);
v___x_2813_ = lean_usize_add(v_i_2805_, v___x_2812_);
v___x_2814_ = lean_array_uset(v_bs_x27_2810_, v_i_2805_, v___x_2811_);
v_i_2805_ = v___x_2813_;
v_bs_2806_ = v___x_2814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object* v_sz_2816_, lean_object* v_i_2817_, lean_object* v_bs_2818_){
_start:
{
size_t v_sz_boxed_2819_; size_t v_i_boxed_2820_; lean_object* v_res_2821_; 
v_sz_boxed_2819_ = lean_unbox_usize(v_sz_2816_);
lean_dec(v_sz_2816_);
v_i_boxed_2820_ = lean_unbox_usize(v_i_2817_);
lean_dec(v_i_2817_);
v_res_2821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_2819_, v_i_boxed_2820_, v_bs_2818_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object* v_argsPacker_2822_){
_start:
{
size_t v_sz_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v_sz_2823_ = lean_array_size(v_argsPacker_2822_);
v___x_2824_ = ((size_t)0ULL);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2823_, v___x_2824_, v_argsPacker_2822_);
return v___x_2825_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0(void){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Array_instInhabited___redArg();
return v___x_2826_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object* v_argsPacker_2827_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2828_ = lean_array_get_size(v_argsPacker_2827_);
v___x_2829_ = lean_unsigned_to_nat(1u);
v___x_2830_ = lean_nat_dec_eq(v___x_2828_, v___x_2829_);
if (v___x_2830_ == 0)
{
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2831_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = lean_array_get_borrowed(v___x_2831_, v_argsPacker_2827_, v___x_2832_);
v___x_2834_ = lean_array_get_size(v___x_2833_);
v___x_2835_ = lean_nat_dec_eq(v___x_2834_, v___x_2829_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object* v_argsPacker_2836_){
_start:
{
uint8_t v_res_2837_; lean_object* v_r_2838_; 
v_res_2837_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2836_);
lean_dec_ref(v_argsPacker_2836_);
v_r_2838_ = lean_box(v_res_2837_);
return v_r_2838_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__2(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2841_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__1));
v___x_2842_ = lean_unsigned_to_nat(2u);
v___x_2843_ = lean_unsigned_to_nat(469u);
v___x_2844_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2845_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2846_ = l_mkPanicMessageWithDecl(v___x_2845_, v___x_2844_, v___x_2843_, v___x_2842_, v___x_2841_);
return v___x_2846_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__4(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2848_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__3));
v___x_2849_ = lean_unsigned_to_nat(2u);
v___x_2850_ = lean_unsigned_to_nat(470u);
v___x_2851_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2852_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2853_ = l_mkPanicMessageWithDecl(v___x_2852_, v___x_2851_, v___x_2850_, v___x_2849_, v___x_2848_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object* v_argsPacker_2854_, lean_object* v_domain_2855_, lean_object* v_fidx_2856_, lean_object* v_args_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = lean_array_get_size(v_argsPacker_2854_);
v___x_2864_ = lean_nat_dec_lt(v_fidx_2856_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
lean_dec(v_fidx_2856_);
lean_dec_ref(v_domain_2855_);
v___x_2865_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__2, &l_Lean_Meta_ArgsPacker_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__2);
v___x_2866_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2865_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2867_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2868_ = lean_array_get_size(v_args_2857_);
v___x_2869_ = lean_array_get_borrowed(v___x_2867_, v_argsPacker_2854_, v_fidx_2856_);
v___x_2870_ = lean_array_get_size(v___x_2869_);
v___x_2871_ = lean_nat_dec_eq(v___x_2868_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec(v_fidx_2856_);
lean_dec_ref(v_domain_2855_);
v___x_2872_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__4, &l_Lean_Meta_ArgsPacker_pack___closed__4_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__4);
v___x_2873_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2872_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
return v___x_2873_;
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_domain_2855_);
v___x_2875_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_2863_, v_domain_2855_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
lean_inc(v_fidx_2856_);
v___x_2877_ = l_List_get_x21Internal___redArg(v___x_2874_, v_a_2876_, v_fidx_2856_);
lean_dec(v_a_2876_);
v___x_2878_ = l_Lean_Meta_ArgsPacker_Unary_pack(v___x_2877_, v_args_2857_);
lean_dec(v___x_2877_);
v___x_2879_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2863_, v_domain_2855_, v_fidx_2856_, v___x_2878_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
lean_dec(v_fidx_2856_);
return v___x_2879_;
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_fidx_2856_);
lean_dec_ref(v_domain_2855_);
v_a_2880_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2875_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2875_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object* v_argsPacker_2888_, lean_object* v_domain_2889_, lean_object* v_fidx_2890_, lean_object* v_args_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2888_, v_domain_2889_, v_fidx_2890_, v_args_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec_ref(v_args_2891_);
lean_dec_ref(v_argsPacker_2888_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object* v_argsPacker_2898_, lean_object* v_e_2899_){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_array_get_size(v_argsPacker_2898_);
v___x_2901_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_2900_, v_e_2899_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_box(0);
return v___x_2902_;
}
else
{
lean_object* v_val_2903_; lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2925_; 
v_val_2903_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v___x_2901_, 1);
v_fst_2904_ = lean_ctor_get(v_val_2903_, 0);
v_snd_2905_ = lean_ctor_get(v_val_2903_, 1);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_val_2903_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2907_ = v_val_2903_;
v_isShared_2908_ = v_isSharedCheck_2925_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_snd_2905_);
lean_inc(v_fst_2904_);
lean_dec(v_val_2903_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2925_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2909_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2910_ = lean_array_get_borrowed(v___x_2909_, v_argsPacker_2898_, v_fst_2904_);
v___x_2911_ = lean_array_get_size(v___x_2910_);
v___x_2912_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_2911_, v_snd_2905_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2913_; 
lean_del_object(v___x_2907_);
lean_dec(v_fst_2904_);
v___x_2913_ = lean_box(0);
return v___x_2913_;
}
else
{
lean_object* v_val_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2924_; 
v_val_2914_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2916_ = v___x_2912_;
v_isShared_2917_ = v_isSharedCheck_2924_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_val_2914_);
lean_dec(v___x_2912_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2924_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v_val_2914_);
v___x_2919_ = v___x_2907_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_fst_2904_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_val_2914_);
v___x_2919_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2921_; 
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2919_);
v___x_2921_ = v___x_2916_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object* v_argsPacker_2926_, lean_object* v_e_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_2926_, v_e_2927_);
lean_dec_ref(v_argsPacker_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object* v_as_2929_, lean_object* v_bs_2930_, lean_object* v_i_2931_, lean_object* v_cs_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2938_ = lean_array_get_size(v_as_2929_);
v___x_2939_ = lean_nat_dec_lt(v_i_2931_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; 
lean_dec(v_i_2931_);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v_cs_2932_);
return v___x_2940_;
}
else
{
lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = lean_array_get_size(v_bs_2930_);
v___x_2942_ = lean_nat_dec_lt(v_i_2931_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec(v_i_2931_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_cs_2932_);
return v___x_2943_;
}
else
{
lean_object* v_a_2944_; lean_object* v_b_2945_; lean_object* v___x_2946_; 
v_a_2944_ = lean_array_fget_borrowed(v_as_2929_, v_i_2931_);
v_b_2945_ = lean_array_fget_borrowed(v_bs_2930_, v_i_2931_);
lean_inc(v_b_2945_);
lean_inc(v_a_2944_);
v___x_2946_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_a_2944_, v_b_2945_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v___x_2948_ = lean_unsigned_to_nat(1u);
v___x_2949_ = lean_nat_add(v_i_2931_, v___x_2948_);
lean_dec(v_i_2931_);
v___x_2950_ = lean_array_push(v_cs_2932_, v_a_2947_);
v_i_2931_ = v___x_2949_;
v_cs_2932_ = v___x_2950_;
goto _start;
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref(v_cs_2932_);
lean_dec(v_i_2931_);
v_a_2952_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2946_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2946_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object* v_as_2960_, lean_object* v_bs_2961_, lean_object* v_i_2962_, lean_object* v_cs_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_2960_, v_bs_2961_, v_i_2962_, v_cs_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v_bs_2961_);
lean_dec_ref(v_as_2960_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object* v_argsPacker_2970_, lean_object* v_types_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_2979_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_argsPacker_2970_, v_types_2971_, v___x_2977_, v___x_2978_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2980_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
return v___x_2981_;
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
v_a_2982_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2979_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2979_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object* v_argsPacker_2990_, lean_object* v_types_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2990_, v_types_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec_ref(v_types_2991_);
lean_dec_ref(v_argsPacker_2990_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object* v_as_2998_, lean_object* v_bs_2999_, lean_object* v_i_3000_, lean_object* v_cs_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = lean_array_get_size(v_as_2998_);
v___x_3008_ = lean_nat_dec_lt(v_i_3000_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
lean_dec(v_i_3000_);
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_cs_3001_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = lean_array_get_size(v_bs_2999_);
v___x_3011_ = lean_nat_dec_lt(v_i_3000_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
lean_dec(v_i_3000_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_cs_3001_);
return v___x_3012_;
}
else
{
lean_object* v_a_3013_; lean_object* v_b_3014_; lean_object* v___x_3015_; 
v_a_3013_ = lean_array_fget_borrowed(v_as_2998_, v_i_3000_);
v_b_3014_ = lean_array_fget_borrowed(v_bs_2999_, v_i_3000_);
lean_inc(v_b_3014_);
lean_inc(v_a_3013_);
v___x_3015_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_a_3013_, v_b_3014_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = lean_unsigned_to_nat(1u);
v___x_3018_ = lean_nat_add(v_i_3000_, v___x_3017_);
lean_dec(v_i_3000_);
v___x_3019_ = lean_array_push(v_cs_3001_, v_a_3016_);
v_i_3000_ = v___x_3018_;
v_cs_3001_ = v___x_3019_;
goto _start;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v_cs_3001_);
lean_dec(v_i_3000_);
v_a_3021_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3015_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3015_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object* v_as_3029_, lean_object* v_bs_3030_, lean_object* v_i_3031_, lean_object* v_cs_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3029_, v_bs_3030_, v_i_3031_, v_cs_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec_ref(v_bs_3030_);
lean_dec_ref(v_as_3029_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object* v_argsPacker_3039_, lean_object* v_es_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = lean_unsigned_to_nat(0u);
v___x_3047_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3048_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3039_, v_es_3040_, v___x_3046_, v___x_3047_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_a_3049_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_);
return v___x_3050_;
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3048_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3048_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object* v_argsPacker_3059_, lean_object* v_es_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3059_, v_es_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec_ref(v_es_3060_);
lean_dec_ref(v_argsPacker_3059_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object* v_argsPacker_3067_, lean_object* v_resultType_3068_, lean_object* v_es_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3077_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3067_, v_es_3069_, v___x_3075_, v___x_3076_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3079_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_3068_, v_a_3078_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
return v___x_3079_;
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v_resultType_3068_);
v_a_3080_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3077_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3077_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object* v_argsPacker_3088_, lean_object* v_resultType_3089_, lean_object* v_es_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3088_, v_resultType_3089_, v_es_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
lean_dec_ref(v_es_3090_);
lean_dec_ref(v_argsPacker_3088_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object* v_argsPacker_3097_, lean_object* v_es_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3106_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3097_, v_es_3098_, v___x_3104_, v___x_3105_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3108_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_a_3107_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
return v___x_3108_;
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3106_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3106_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object* v_argsPacker_3117_, lean_object* v_es_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3117_, v_es_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec_ref(v_a_3119_);
lean_dec_ref(v_es_3118_);
lean_dec_ref(v_argsPacker_3117_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object* v_msg_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___f_3131_; lean_object* v___x_920__overap_3132_; lean_object* v___x_3133_; 
v___f_3131_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_920__overap_3132_ = lean_panic_fn_borrowed(v___f_3131_, v_msg_3125_);
lean_inc(v___y_3129_);
lean_inc_ref(v___y_3128_);
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3126_);
v___x_3133_ = lean_apply_5(v___x_920__overap_3132_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, lean_box(0));
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object* v_msg_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object* v_a_3141_, lean_object* v___x_3142_, lean_object* v_i_3143_, lean_object* v_e_3144_, lean_object* v_x_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = l_List_lengthTR___redArg(v_a_3141_);
lean_inc_ref(v_x_3145_);
v___x_3152_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_3151_, v___x_3142_, v_i_3143_, v_x_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___x_3151_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; uint8_t v___x_3160_; uint8_t v___x_3161_; lean_object* v___x_3162_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3154_ = lean_unsigned_to_nat(1u);
v___x_3155_ = lean_mk_empty_array_with_capacity(v___x_3154_);
lean_inc_ref(v___x_3155_);
v___x_3156_ = lean_array_push(v___x_3155_, v_x_3145_);
v___x_3157_ = lean_array_push(v___x_3155_, v_a_3153_);
v___x_3158_ = l_Lean_Expr_beta(v_e_3144_, v___x_3157_);
v___x_3159_ = 0;
v___x_3160_ = 1;
v___x_3161_ = 1;
v___x_3162_ = l_Lean_Meta_mkLambdaFVars(v___x_3156_, v___x_3158_, v___x_3159_, v___x_3160_, v___x_3159_, v___x_3160_, v___x_3161_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec_ref(v___x_3156_);
return v___x_3162_;
}
else
{
lean_dec_ref(v_x_3145_);
lean_dec_ref(v_e_3144_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object* v_a_3163_, lean_object* v___x_3164_, lean_object* v_i_3165_, lean_object* v_e_3166_, lean_object* v_x_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3163_, v___x_3164_, v_i_3165_, v_e_3166_, v_x_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v_i_3165_);
lean_dec(v_a_3163_);
return v_res_3173_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__0));
v___x_3176_ = l_Lean_stringToMessageData(v___x_3175_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3179_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__3));
v___x_3180_ = lean_unsigned_to_nat(4u);
v___x_3181_ = lean_unsigned_to_nat(535u);
v___x_3182_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__2));
v___x_3183_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_3184_ = l_mkPanicMessageWithDecl(v___x_3183_, v___x_3182_, v___x_3181_, v___x_3180_, v___x_3179_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object* v_argsPacker_3185_, lean_object* v_e_3186_, lean_object* v_i_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v_n_3195_; lean_object* v___x_3196_; 
v___x_3193_ = l_Lean_instInhabitedExpr;
v___x_3194_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v_n_3195_ = lean_array_get_size(v_argsPacker_3185_);
lean_inc(v_a_3191_);
lean_inc_ref(v_a_3190_);
lean_inc(v_a_3189_);
lean_inc_ref(v_a_3188_);
lean_inc_ref(v_e_3186_);
v___x_3196_ = lean_infer_type(v_e_3186_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
lean_inc(v_a_3191_);
lean_inc_ref(v_a_3190_);
lean_inc(v_a_3189_);
lean_inc_ref(v_a_3188_);
v___x_3198_ = lean_whnf(v_a_3197_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___x_3242_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3198_, 1);
v___x_3242_ = l_Lean_Expr_isForall(v_a_3199_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__4, &l_Lean_Meta_ArgsPacker_curryProj___closed__4_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4);
v___x_3244_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v___x_3243_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_dec_ref_known(v___x_3244_, 1);
v___y_3214_ = v_a_3188_;
v___y_3215_ = v_a_3189_;
v___y_3216_ = v_a_3190_;
v___y_3217_ = v_a_3191_;
goto v___jp_3213_;
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v_a_3199_);
lean_dec(v_i_3187_);
lean_dec_ref(v_e_3186_);
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3244_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
v___y_3214_ = v_a_3188_;
v___y_3215_ = v_a_3189_;
v___y_3216_ = v_a_3190_;
v___y_3217_ = v_a_3191_;
goto v___jp_3213_;
}
v___jp_3200_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_inc(v_i_3187_);
v___x_3207_ = l_List_get_x21Internal___redArg(v___x_3193_, v___y_3201_, v_i_3187_);
lean_dec(v___y_3201_);
v___x_3208_ = l_Lean_Expr_bindingName_x21(v_a_3199_);
lean_dec(v_a_3199_);
v___x_3209_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3208_, v___x_3207_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = lean_array_get_borrowed(v___x_3194_, v_argsPacker_3185_, v_i_3187_);
lean_dec(v_i_3187_);
lean_inc(v___x_3211_);
v___x_3212_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v___x_3211_, v_a_3210_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3212_;
}
else
{
lean_dec(v_i_3187_);
return v___x_3209_;
}
}
v___jp_3213_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = l_Lean_Expr_bindingDomain_x21(v_a_3199_);
lean_inc_ref(v___x_3218_);
v___x_3219_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_3195_, v___x_3218_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc_n(v_a_3220_, 2);
lean_dec_ref_known(v___x_3219_, 1);
lean_inc(v_i_3187_);
v___f_3221_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3221_, 0, v_a_3220_);
lean_closure_set(v___f_3221_, 1, v___x_3218_);
lean_closure_set(v___f_3221_, 2, v_i_3187_);
lean_closure_set(v___f_3221_, 3, v_e_3186_);
v___x_3222_ = l_List_lengthTR___redArg(v_a_3220_);
v___x_3223_ = lean_nat_dec_lt(v_i_3187_, v___x_3222_);
lean_dec(v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v___f_3221_);
lean_dec(v_a_3220_);
lean_dec(v_a_3199_);
lean_dec(v_i_3187_);
v___x_3224_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__1, &l_Lean_Meta_ArgsPacker_curryProj___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1);
v___x_3225_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3224_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
else
{
v___y_3201_ = v_a_3220_;
v___y_3202_ = v___f_3221_;
v___y_3203_ = v___y_3214_;
v___y_3204_ = v___y_3215_;
v___y_3205_ = v___y_3216_;
v___y_3206_ = v___y_3217_;
goto v___jp_3200_;
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v___x_3218_);
lean_dec(v_a_3199_);
lean_dec(v_i_3187_);
lean_dec_ref(v_e_3186_);
v_a_3234_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3219_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3219_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
else
{
lean_dec(v_i_3187_);
lean_dec_ref(v_e_3186_);
return v___x_3198_;
}
}
else
{
lean_dec(v_i_3187_);
lean_dec_ref(v_e_3186_);
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object* v_argsPacker_3253_, lean_object* v_e_3254_, lean_object* v_i_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3253_, v_e_3254_, v_i_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec_ref(v_a_3256_);
lean_dec_ref(v_argsPacker_3253_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object* v_as_3262_, lean_object* v_bs_3263_, lean_object* v_i_3264_, lean_object* v_cs_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = lean_array_get_size(v_as_3262_);
v___x_3272_ = lean_nat_dec_lt(v_i_3264_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
lean_dec(v_i_3264_);
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_cs_3265_);
return v___x_3273_;
}
else
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = lean_array_get_size(v_bs_3263_);
v___x_3275_ = lean_nat_dec_lt(v_i_3264_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; 
lean_dec(v_i_3264_);
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_cs_3265_);
return v___x_3276_;
}
else
{
lean_object* v_a_3277_; lean_object* v_b_3278_; lean_object* v___x_3279_; 
v_a_3277_ = lean_array_fget_borrowed(v_as_3262_, v_i_3264_);
v_b_3278_ = lean_array_fget_borrowed(v_bs_3263_, v_i_3264_);
lean_inc(v_b_3278_);
lean_inc(v_a_3277_);
v___x_3279_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_3277_, v_b_3278_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = lean_nat_add(v_i_3264_, v___x_3281_);
lean_dec(v_i_3264_);
v___x_3283_ = lean_array_push(v_cs_3265_, v_a_3280_);
v_i_3264_ = v___x_3282_;
v_cs_3265_ = v___x_3283_;
goto _start;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v_cs_3265_);
lean_dec(v_i_3264_);
v_a_3285_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3279_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3279_);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object* v_as_3293_, lean_object* v_bs_3294_, lean_object* v_i_3295_, lean_object* v_cs_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3293_, v_bs_3294_, v_i_3295_, v_cs_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec_ref(v_bs_3294_);
lean_dec_ref(v_as_3293_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object* v_argsPacker_3303_, lean_object* v_t_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = lean_array_get_size(v_argsPacker_3303_);
v___x_3311_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v___x_3310_, v_t_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3315_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_argsPacker_3303_, v_a_3312_, v___x_3313_, v___x_3314_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
lean_dec(v_a_3312_);
return v___x_3315_;
}
else
{
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object* v_argsPacker_3316_, lean_object* v_t_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3316_, v_t_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec_ref(v_argsPacker_3316_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object* v_upperBound_3324_, lean_object* v_argsPacker_3325_, lean_object* v_e_3326_, lean_object* v_a_3327_, lean_object* v_b_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
uint8_t v___x_3334_; 
v___x_3334_ = lean_nat_dec_lt(v_a_3327_, v_upperBound_3324_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
lean_dec(v_a_3327_);
lean_dec_ref(v_e_3326_);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_b_3328_);
return v___x_3335_;
}
else
{
lean_object* v___x_3336_; 
lean_inc(v_a_3327_);
lean_inc_ref(v_e_3326_);
v___x_3336_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3325_, v_e_3326_, v_a_3327_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
lean_dec_ref_known(v___x_3336_, 1);
v___x_3338_ = lean_array_push(v_b_3328_, v_a_3337_);
v___x_3339_ = lean_unsigned_to_nat(1u);
v___x_3340_ = lean_nat_add(v_a_3327_, v___x_3339_);
lean_dec(v_a_3327_);
v_a_3327_ = v___x_3340_;
v_b_3328_ = v___x_3338_;
goto _start;
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec_ref(v_b_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_e_3326_);
v_a_3342_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3336_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3336_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object* v_upperBound_3350_, lean_object* v_argsPacker_3351_, lean_object* v_e_3352_, lean_object* v_a_3353_, lean_object* v_b_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3350_, v_argsPacker_3351_, v_e_3352_, v_a_3353_, v_b_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec_ref(v_argsPacker_3351_);
lean_dec(v_upperBound_3350_);
return v_res_3360_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curry___closed__0(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = l_Lean_Level_ofNat(v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object* v_argsPacker_3363_, lean_object* v_e_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v_es_3372_; lean_object* v___x_3373_; 
v___x_3370_ = lean_array_get_size(v_argsPacker_3363_);
v___x_3371_ = lean_unsigned_to_nat(0u);
v_es_3372_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3373_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_3370_, v_argsPacker_3363_, v_e_3364_, v___x_3371_, v_es_3372_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
v___x_3375_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curry___closed__0, &l_Lean_Meta_ArgsPacker_curry___closed__0_once, _init_l_Lean_Meta_ArgsPacker_curry___closed__0);
v___x_3376_ = l_Lean_Meta_PProdN_mk(v___x_3375_, v_a_3374_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
return v___x_3376_;
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
v_a_3377_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3373_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3373_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object* v_argsPacker_3385_, lean_object* v_e_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3385_, v_e_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec_ref(v_argsPacker_3385_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object* v_upperBound_3393_, lean_object* v_argsPacker_3394_, lean_object* v_e_3395_, lean_object* v_inst_3396_, lean_object* v_R_3397_, lean_object* v_a_3398_, lean_object* v_b_3399_, lean_object* v_c_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3393_, v_argsPacker_3394_, v_e_3395_, v_a_3398_, v_b_3399_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object* v_upperBound_3407_, lean_object* v_argsPacker_3408_, lean_object* v_e_3409_, lean_object* v_inst_3410_, lean_object* v_R_3411_, lean_object* v_a_3412_, lean_object* v_b_3413_, lean_object* v_c_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3407_, v_argsPacker_3408_, v_e_3409_, v_inst_3410_, v_R_3411_, v_a_3412_, v_b_3413_, v_c_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v_argsPacker_3408_);
lean_dec(v_upperBound_3407_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object* v_a_3421_, lean_object* v_argsPacker_3422_, lean_object* v_name_3423_, lean_object* v_k_3424_, lean_object* v_tail_3425_, lean_object* v_x_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3421_, v_argsPacker_3422_, v_name_3423_, v_k_3424_, v_tail_3425_, v_x_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object* v_argsPacker_3433_, lean_object* v_name_3434_, lean_object* v_k_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
if (lean_obj_tag(v_a_3436_) == 0)
{
lean_object* v___x_3443_; 
lean_dec(v_name_3434_);
lean_dec_ref(v_argsPacker_3433_);
lean_inc(v_a_3441_);
lean_inc_ref(v_a_3440_);
lean_inc(v_a_3439_);
lean_inc_ref(v_a_3438_);
v___x_3443_ = lean_apply_6(v_k_3435_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, lean_box(0));
return v___x_3443_;
}
else
{
lean_object* v_head_3444_; lean_object* v_tail_3445_; lean_object* v___f_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; 
v_head_3444_ = lean_ctor_get(v_a_3436_, 0);
lean_inc(v_head_3444_);
v_tail_3445_ = lean_ctor_get(v_a_3436_, 1);
lean_inc(v_tail_3445_);
lean_dec_ref_known(v_a_3436_, 2);
lean_inc(v_name_3434_);
lean_inc_ref(v_argsPacker_3433_);
lean_inc_ref(v_a_3437_);
v___f_3446_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3446_, 0, v_a_3437_);
lean_closure_set(v___f_3446_, 1, v_argsPacker_3433_);
lean_closure_set(v___f_3446_, 2, v_name_3434_);
lean_closure_set(v___f_3446_, 3, v_k_3435_);
lean_closure_set(v___f_3446_, 4, v_tail_3445_);
v___x_3447_ = lean_array_get_size(v_argsPacker_3433_);
lean_dec_ref(v_argsPacker_3433_);
v___x_3448_ = lean_unsigned_to_nat(1u);
v___x_3449_ = lean_nat_dec_eq(v___x_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
uint8_t v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3450_ = 1;
v___x_3451_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3434_, v___x_3450_);
v___x_3452_ = lean_array_get_size(v_a_3437_);
lean_dec_ref(v_a_3437_);
v___x_3453_ = lean_nat_add(v___x_3452_, v___x_3448_);
v___x_3454_ = l_Nat_reprFast(v___x_3453_);
v___x_3455_ = lean_string_append(v___x_3451_, v___x_3454_);
lean_dec_ref(v___x_3454_);
v___x_3456_ = lean_box(0);
v___x_3457_ = l_Lean_Name_str___override(v___x_3456_, v___x_3455_);
v___x_3458_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3457_, v_head_3444_, v___f_3446_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
return v___x_3458_;
}
else
{
lean_object* v___x_3459_; 
lean_dec_ref(v_a_3437_);
v___x_3459_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_3434_, v_head_3444_, v___f_3446_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
return v___x_3459_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object* v_a_3460_, lean_object* v_argsPacker_3461_, lean_object* v_name_3462_, lean_object* v_k_3463_, lean_object* v_tail_3464_, lean_object* v_x_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = lean_array_push(v_a_3460_, v_x_3465_);
v___x_3472_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3461_, v_name_3462_, v_k_3463_, v_tail_3464_, v___x_3471_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object* v_argsPacker_3473_, lean_object* v_name_3474_, lean_object* v_k_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3473_, v_name_3474_, v_k_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object* v_00_u03b1_3484_, lean_object* v_argsPacker_3485_, lean_object* v_name_3486_, lean_object* v_k_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3485_, v_name_3486_, v_k_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object* v_00_u03b1_3496_, lean_object* v_argsPacker_3497_, lean_object* v_name_3498_, lean_object* v_k_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(v_00_u03b1_3496_, v_argsPacker_3497_, v_name_3498_, v_k_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object* v_argsPacker_3508_, lean_object* v_name_3509_, lean_object* v_type_3510_, lean_object* v_k_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3508_, v_type_3510_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___x_3519_ = lean_array_to_list(v_a_3518_);
v___x_3520_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3521_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3508_, v_name_3509_, v_k_3511_, v___x_3519_, v___x_3520_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
return v___x_3521_;
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec_ref(v_k_3511_);
lean_dec(v_name_3509_);
lean_dec_ref(v_argsPacker_3508_);
v_a_3522_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3517_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3517_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object* v_argsPacker_3530_, lean_object* v_name_3531_, lean_object* v_type_3532_, lean_object* v_k_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3530_, v_name_3531_, v_type_3532_, v_k_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object* v_00_u03b1_3540_, lean_object* v_argsPacker_3541_, lean_object* v_name_3542_, lean_object* v_type_3543_, lean_object* v_k_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3541_, v_name_3542_, v_type_3543_, v_k_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object* v_00_u03b1_3551_, lean_object* v_argsPacker_3552_, lean_object* v_name_3553_, lean_object* v_type_3554_, lean_object* v_k_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(v_00_u03b1_3551_, v_argsPacker_3552_, v_name_3553_, v_type_3554_, v_k_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object* v_argsPacker_3562_, lean_object* v_packedMotiveType_3563_, lean_object* v_type_3564_, lean_object* v_value_3565_, lean_object* v_k_3566_, lean_object* v_motives_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3562_, v_packedMotiveType_3563_, v_motives_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc_n(v_a_3574_, 2);
lean_dec_ref_known(v___x_3573_, 1);
v___x_3575_ = lean_unsigned_to_nat(1u);
v___x_3576_ = lean_mk_empty_array_with_capacity(v___x_3575_);
v___x_3577_ = lean_array_push(v___x_3576_, v_a_3574_);
v___x_3578_ = l_Lean_Meta_instantiateForall(v_type_3564_, v___x_3577_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec_ref(v___x_3577_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3579_);
lean_dec_ref_known(v___x_3578_, 1);
v___x_3580_ = l_Lean_Expr_app___override(v_value_3565_, v_a_3574_);
lean_inc(v___y_3571_);
lean_inc_ref(v___y_3570_);
lean_inc(v___y_3569_);
lean_inc_ref(v___y_3568_);
v___x_3581_ = lean_apply_8(v_k_3566_, v_motives_3567_, v___x_3580_, v_a_3579_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, lean_box(0));
return v___x_3581_;
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v_a_3574_);
lean_dec_ref(v_motives_3567_);
lean_dec_ref(v_k_3566_);
lean_dec_ref(v_value_3565_);
v_a_3582_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3578_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3578_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v_motives_3567_);
lean_dec_ref(v_k_3566_);
lean_dec_ref(v_value_3565_);
lean_dec_ref(v_type_3564_);
v_a_3590_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3573_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3573_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object* v_argsPacker_3598_, lean_object* v_packedMotiveType_3599_, lean_object* v_type_3600_, lean_object* v_value_3601_, lean_object* v_k_3602_, lean_object* v_motives_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3598_, v_packedMotiveType_3599_, v_type_3600_, v_value_3601_, v_k_3602_, v_motives_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v_argsPacker_3598_);
return v_res_3609_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0));
v___x_3612_ = l_Lean_stringToMessageData(v___x_3611_);
return v___x_3612_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2));
v___x_3615_ = l_Lean_stringToMessageData(v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object* v_argsPacker_3616_, lean_object* v_value_3617_, lean_object* v_type_3618_, lean_object* v_k_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; uint8_t v___x_3654_; 
v___x_3654_ = l_Lean_Expr_isForall(v_type_3618_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec_ref(v_k_3619_);
lean_dec_ref(v_value_3617_);
lean_dec_ref(v_argsPacker_3616_);
v___x_3655_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3);
v___x_3656_ = l_Lean_MessageData_ofExpr(v_type_3618_);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3657_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
else
{
v___y_3635_ = v_a_3620_;
v___y_3636_ = v_a_3621_;
v___y_3637_ = v_a_3622_;
v___y_3638_ = v_a_3623_;
goto v___jp_3634_;
}
v___jp_3625_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = l_Lean_Expr_bindingName_x21(v_type_3618_);
lean_dec_ref(v_type_3618_);
v___x_3633_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3616_, v___x_3632_, v___y_3627_, v___y_3626_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
return v___x_3633_;
}
v___jp_3634_:
{
lean_object* v_packedMotiveType_3639_; lean_object* v___f_3640_; uint8_t v___x_3641_; 
v_packedMotiveType_3639_ = l_Lean_Expr_bindingDomain_x21(v_type_3618_);
lean_inc_ref(v_type_3618_);
lean_inc_ref(v_packedMotiveType_3639_);
lean_inc_ref(v_argsPacker_3616_);
v___f_3640_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3640_, 0, v_argsPacker_3616_);
lean_closure_set(v___f_3640_, 1, v_packedMotiveType_3639_);
lean_closure_set(v___f_3640_, 2, v_type_3618_);
lean_closure_set(v___f_3640_, 3, v_value_3617_);
lean_closure_set(v___f_3640_, 4, v_k_3619_);
v___x_3641_ = l_Lean_Expr_isForall(v_packedMotiveType_3639_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v___f_3640_);
lean_dec_ref(v_type_3618_);
lean_dec_ref(v_argsPacker_3616_);
v___x_3642_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1);
v___x_3643_ = l_Lean_indentExpr(v_packedMotiveType_3639_);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3644_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
else
{
v___y_3626_ = v___f_3640_;
v___y_3627_ = v_packedMotiveType_3639_;
v___y_3628_ = v___y_3635_;
v___y_3629_ = v___y_3636_;
v___y_3630_ = v___y_3637_;
v___y_3631_ = v___y_3638_;
goto v___jp_3625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object* v_argsPacker_3667_, lean_object* v_value_3668_, lean_object* v_type_3669_, lean_object* v_k_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3667_, v_value_3668_, v_type_3669_, v_k_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object* v_00_u03b1_3677_, lean_object* v_argsPacker_3678_, lean_object* v_value_3679_, lean_object* v_type_3680_, lean_object* v_k_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3678_, v_value_3679_, v_type_3680_, v_k_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object* v_00_u03b1_3688_, lean_object* v_argsPacker_3689_, lean_object* v_value_3690_, lean_object* v_type_3691_, lean_object* v_k_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_Meta_ArgsPacker_curryParam(v_00_u03b1_3688_, v_argsPacker_3689_, v_value_3690_, v_type_3691_, v_k_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
return v_res_3698_;
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
