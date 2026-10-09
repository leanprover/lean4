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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(lean_object* v___x_4_, lean_object* v_as_5_, size_t v_sz_6_, size_t v_i_7_, lean_object* v_b_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4_ = stack[0].m_obj;
lean_object* v_as_5_ = stack[1].m_obj;
size_t v_sz_6_ = stack[2].m_num;
size_t v_i_7_ = stack[3].m_num;
lean_object* v_b_8_ = stack[4].m_obj;
lean_object* v___y_9_ = stack[5].m_obj;
lean_object* v___y_10_ = stack[6].m_obj;
lean_object* v___y_11_ = stack[7].m_obj;
lean_object* v___y_12_ = stack[8].m_obj;
lean_object* v_res_51_;
v_res_51_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(v___x_4_, v_as_5_, v_sz_6_, v_i_7_, v_b_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___boxed(lean_object* v___x_52_, lean_object* v_as_53_, lean_object* v_sz_54_, lean_object* v_i_55_, lean_object* v_b_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
size_t v_sz_boxed_62_; size_t v_i_boxed_63_; lean_object* v_res_64_; 
v_sz_boxed_62_ = lean_unbox_usize(v_sz_54_);
lean_dec(v_sz_54_);
v_i_boxed_63_ = lean_unbox_usize(v_i_55_);
lean_dec(v_i_55_);
v_res_64_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(v___x_52_, v_as_53_, v_sz_boxed_62_, v_i_boxed_63_, v_b_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec_ref(v_as_53_);
lean_dec(v___x_52_);
return v_res_64_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_box(0);
v___x_69_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1));
v___x_70_ = l_Lean_mkConst(v___x_69_, v___x_68_);
return v___x_70_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Unary_packType(lean_object* v_xs_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = lean_array_get_size(v_xs_71_);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = l_Lean_instInhabitedExpr;
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_sub(v___x_77_, v___x_81_);
v___x_83_ = lean_array_get_borrowed(v___x_80_, v_xs_71_, v___x_82_);
lean_dec(v___x_82_);
lean_inc(v_a_75_);
lean_inc_ref(v_a_74_);
lean_inc(v_a_73_);
lean_inc_ref(v_a_72_);
lean_inc(v___x_83_);
v___x_84_ = lean_infer_type(v___x_83_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v___x_87_; size_t v_sz_88_; size_t v___x_89_; lean_object* v___x_90_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v___x_84_, 1);
v___x_86_ = lean_array_pop(v_xs_71_);
v___x_87_ = l_Array_reverse___redArg(v___x_86_);
v_sz_88_ = lean_array_size(v___x_87_);
v___x_89_ = ((size_t)0ULL);
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0(v___x_77_, v___x_87_, v_sz_88_, v___x_89_, v_a_85_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec_ref(v___x_87_);
return v___x_90_;
}
else
{
lean_dec_ref(v_xs_71_);
return v___x_84_;
}
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec_ref(v_xs_71_);
v___x_91_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Unary_packType_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_71_ = stack[0].m_obj;
lean_object* v_a_72_ = stack[1].m_obj;
lean_object* v_a_73_ = stack[2].m_obj;
lean_object* v_a_74_ = stack[3].m_obj;
lean_object* v_a_75_ = stack[4].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Lean_Meta_ArgsPacker_Unary_packType(v_xs_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_packType___boxed(lean_object* v_xs_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_ArgsPacker_Unary_packType(v_xs_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(lean_object* v_msg_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = l_Lean_instInhabitedExpr;
v___x_103_ = lean_panic_fn_borrowed(v___x_102_, v_msg_101_);
return v___x_103_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_107_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__2));
v___x_108_ = lean_unsigned_to_nat(6u);
v___x_109_ = lean_unsigned_to_nat(86u);
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1));
v___x_111_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_112_ = l_mkPanicMessageWithDecl(v___x_111_, v___x_110_, v___x_109_, v___x_108_, v___x_107_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_114_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__4));
v___x_115_ = lean_unsigned_to_nat(6u);
v___x_116_ = lean_unsigned_to_nat(90u);
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__1));
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_119_ = l_mkPanicMessageWithDecl(v___x_118_, v___x_117_, v___x_116_, v___x_115_, v___x_114_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(lean_object* v_args_124_, lean_object* v_i_125_, lean_object* v_type_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_127_ = lean_array_get_size(v_args_124_);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_nat_dec_lt(v_i_125_, v___x_129_);
lean_dec(v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = l_Lean_instInhabitedExpr;
v___x_132_ = lean_array_get_borrowed(v___x_131_, v_args_124_, v_i_125_);
lean_inc(v___x_132_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_134_ = lean_unsigned_to_nat(2u);
v___x_135_ = l_Lean_Expr_isAppOfArity(v_type_126_, v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__3);
v___x_137_ = l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(v___x_136_);
return v___x_137_;
}
else
{
lean_object* v_00_u03b2_138_; uint8_t v___x_139_; 
v_00_u03b2_138_ = l_Lean_Expr_appArg_x21(v_type_126_);
v___x_139_ = l_Lean_Expr_isLambda(v_00_u03b2_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec_ref(v_00_u03b2_138_);
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__5);
v___x_141_ = l_panic___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go_spec__0(v___x_140_);
return v___x_141_;
}
else
{
lean_object* v_arg_142_; lean_object* v___x_143_; lean_object* v_us_144_; lean_object* v___x_145_; lean_object* v_00_u03b1_146_; lean_object* v___x_147_; lean_object* v_type_148_; lean_object* v___x_149_; lean_object* v_rest_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_arg_142_ = lean_array_fget_borrowed(v_args_124_, v_i_125_);
v___x_143_ = l_Lean_Expr_getAppFn(v_type_126_);
v_us_144_ = l_Lean_Expr_constLevels_x21(v___x_143_);
lean_dec_ref(v___x_143_);
v___x_145_ = l_Lean_Expr_appFn_x21(v_type_126_);
v_00_u03b1_146_ = l_Lean_Expr_appArg_x21(v___x_145_);
lean_dec_ref(v___x_145_);
v___x_147_ = l_Lean_Expr_bindingBody_x21(v_00_u03b2_138_);
v_type_148_ = lean_expr_instantiate1(v___x_147_, v_arg_142_);
lean_dec_ref(v___x_147_);
v___x_149_ = lean_nat_add(v_i_125_, v___x_128_);
v_rest_150_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(v_args_124_, v___x_149_, v_type_148_);
lean_dec_ref(v_type_148_);
lean_dec(v___x_149_);
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7));
v___x_152_ = l_Lean_mkConst(v___x_151_, v_us_144_);
lean_inc(v_arg_142_);
v___x_153_ = l_Lean_mkApp4(v___x_152_, v_00_u03b1_146_, v_00_u03b2_138_, v_arg_142_, v_rest_150_);
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___boxed(lean_object* v_args_154_, lean_object* v_i_155_, lean_object* v_type_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(v_args_154_, v_i_155_, v_type_156_);
lean_dec_ref(v_type_156_);
lean_dec(v_i_155_);
lean_dec_ref(v_args_154_);
return v_res_157_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
v___x_163_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_pack___closed__1));
v___x_164_ = l_Lean_mkConst(v___x_163_, v___x_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_pack(lean_object* v_type_165_, lean_object* v_args_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_167_ = lean_array_get_size(v_args_166_);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_nat_dec_eq(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go(v_args_166_, v___x_168_, v_type_165_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_pack___closed__2, &l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_pack___boxed(lean_object* v_type_172_, lean_object* v_args_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_type_172_, v_args_173_);
lean_dec_ref(v_args_173_);
lean_dec_ref(v_type_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(lean_object* v_arity_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_fst_177_; lean_object* v_snd_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_208_; 
v_fst_177_ = lean_ctor_get(v_a_176_, 0);
v_snd_178_ = lean_ctor_get(v_a_176_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_a_176_);
if (v_isSharedCheck_208_ == 0)
{
v___x_180_ = v_a_176_;
v_isShared_181_ = v_isSharedCheck_208_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_snd_178_);
lean_inc(v_fst_177_);
lean_dec(v_a_176_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_208_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_182_ = lean_array_get_size(v_snd_178_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v___x_182_, v___x_183_);
v___x_185_ = lean_nat_dec_lt(v___x_184_, v_arity_175_);
lean_dec(v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_187_; 
if (v_isShared_181_ == 0)
{
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_fst_177_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_snd_178_);
v___x_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__7));
v___x_191_ = lean_unsigned_to_nat(4u);
v___x_192_ = l_Lean_Expr_isAppOfArity(v_fst_177_, v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_del_object(v___x_180_);
lean_dec(v_snd_178_);
lean_dec(v_fst_177_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_194_ = lean_unsigned_to_nat(2u);
v___x_195_ = l_Lean_Expr_getAppNumArgs(v_fst_177_);
v___x_196_ = lean_nat_sub(v___x_195_, v___x_194_);
v___x_197_ = lean_nat_sub(v___x_196_, v___x_183_);
lean_dec(v___x_196_);
v___x_198_ = l_Lean_Expr_getRevArg_x21(v_fst_177_, v___x_197_);
v___x_199_ = lean_array_push(v_snd_178_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(3u);
v___x_201_ = lean_nat_sub(v___x_195_, v___x_200_);
lean_dec(v___x_195_);
v___x_202_ = lean_nat_sub(v___x_201_, v___x_183_);
lean_dec(v___x_201_);
v___x_203_ = l_Lean_Expr_getRevArg_x21(v_fst_177_, v___x_202_);
lean_dec(v_fst_177_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_199_);
lean_ctor_set(v___x_180_, 0, v___x_203_);
v___x_205_ = v___x_180_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___x_199_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
v_a_176_ = v___x_205_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg___boxed(lean_object* v_arity_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_209_, v_a_210_);
lean_dec(v_arity_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack(lean_object* v_arity_216_, lean_object* v_e_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_nat_dec_eq(v_arity_216_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v_args_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_args_220_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v_e_217_);
lean_ctor_set(v___x_221_, 1, v_args_220_);
v___x_222_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_216_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_234_; 
v_val_224_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_234_ == 0)
{
v___x_226_ = v___x_222_;
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_val_224_);
lean_dec(v___x_222_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v_fst_228_ = lean_ctor_get(v_val_224_, 0);
lean_inc(v_fst_228_);
v_snd_229_ = lean_ctor_get(v_val_224_, 1);
lean_inc(v_snd_229_);
lean_dec(v_val_224_);
v___x_230_ = lean_array_push(v_snd_229_, v_fst_228_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_230_);
v___x_232_ = v___x_226_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
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
else
{
lean_object* v___x_235_; 
lean_dec_ref(v_e_217_);
v___x_235_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__1));
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_unpack___boxed(lean_object* v_arity_236_, lean_object* v_e_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v_arity_236_, v_e_237_);
lean_dec(v_arity_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(lean_object* v_arity_239_, lean_object* v_inst_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___redArg(v_arity_239_, v_a_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0___boxed(lean_object* v_arity_243_, lean_object* v_inst_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Unary_unpack_spec__0(v_arity_243_, v_inst_244_, v_a_245_);
lean_dec(v_arity_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(lean_object* v_upperBound_247_, lean_object* v_a_248_, lean_object* v_b_249_){
_start:
{
uint8_t v___x_250_; 
v___x_250_ = lean_nat_dec_lt(v_a_248_, v_upperBound_247_);
if (v___x_250_ == 0)
{
lean_dec(v_a_248_);
return v_b_249_;
}
else
{
lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_267_; 
v_fst_251_ = lean_ctor_get(v_b_249_, 0);
v_snd_252_ = lean_ctor_get(v_b_249_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_b_249_);
if (v_isSharedCheck_267_ == 0)
{
v___x_254_ = v_b_249_;
v_isShared_255_ = v_isSharedCheck_267_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snd_252_);
lean_inc(v_fst_251_);
lean_dec(v_b_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_267_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
lean_inc(v_snd_252_);
v___x_259_ = l_Lean_mkProj(v___x_258_, v___x_256_, v_snd_252_);
v___x_260_ = lean_array_push(v_fst_251_, v___x_259_);
v___x_261_ = l_Lean_mkProj(v___x_258_, v___x_257_, v_snd_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_261_);
lean_ctor_set(v___x_254_, 0, v___x_260_);
v___x_263_ = v___x_254_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_266_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_nat_add(v_a_248_, v___x_257_);
lean_dec(v_a_248_);
v_a_248_ = v___x_264_;
v_b_249_ = v___x_263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg___boxed(lean_object* v_upperBound_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_268_, v_a_269_, v_b_270_);
lean_dec(v_upperBound_268_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(lean_object* v_t_272_, lean_object* v_arity_273_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_nat_dec_eq(v_arity_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_result_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v___x_283_; 
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_sub(v_arity_273_, v___x_276_);
v_result_278_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_result_278_);
lean_ctor_set(v___x_279_, 1, v_t_272_);
v___x_280_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v___x_277_, v___x_274_, v___x_279_);
lean_dec(v___x_277_);
v_fst_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_fst_281_);
v_snd_282_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_snd_282_);
lean_dec_ref(v___x_280_);
v___x_283_ = lean_array_push(v_fst_281_, v_snd_282_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; 
lean_dec_ref(v_t_272_);
v___x_284_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems___boxed(lean_object* v_t_285_, lean_object* v_arity_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_t_285_, v_arity_286_);
lean_dec(v_arity_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(lean_object* v_upperBound_288_, lean_object* v_inst_289_, lean_object* v_R_290_, lean_object* v_a_291_, lean_object* v_b_292_, lean_object* v_c_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___redArg(v_upperBound_288_, v_a_291_, v_b_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0___boxed(lean_object* v_upperBound_295_, lean_object* v_inst_296_, lean_object* v_R_297_, lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v_c_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems_spec__0(v_upperBound_295_, v_inst_296_, v_R_297_, v_a_298_, v_b_299_, v_c_300_);
lean_dec(v_upperBound_295_);
return v_res_301_;
}
}
lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___f_309_; lean_object* v___x_450__overap_310_; lean_object* v___x_311_; 
v___f_309_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_450__overap_310_ = lean_panic_fn_borrowed(v___f_309_, v_msg_303_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
v___x_311_ = lean_apply_5(v___x_450__overap_310_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, lean_box(0));
return v___x_311_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_303_ = stack[0].m_obj;
lean_object* v___y_304_ = stack[1].m_obj;
lean_object* v___y_305_ = stack[2].m_obj;
lean_object* v___y_306_ = stack[3].m_obj;
lean_object* v___y_307_ = stack[4].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v_msg_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___boxed(lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(lean_object* v_k_320_, lean_object* v_b_321_, lean_object* v_c_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; 
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc(v___y_324_);
lean_inc_ref(v___y_323_);
v___x_328_ = lean_apply_7(v_k_320_, v_b_321_, v_c_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, lean_box(0));
return v___x_328_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_320_ = stack[0].m_obj;
lean_object* v_b_321_ = stack[1].m_obj;
lean_object* v_c_322_ = stack[2].m_obj;
lean_object* v___y_323_ = stack[3].m_obj;
lean_object* v___y_324_ = stack[4].m_obj;
lean_object* v___y_325_ = stack[5].m_obj;
lean_object* v___y_326_ = stack[6].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(v_k_320_, v_b_321_, v_c_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed(lean_object* v_k_330_, lean_object* v_b_331_, lean_object* v_c_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0(v_k_330_, v_b_331_, v_c_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_338_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(lean_object* v_type_339_, lean_object* v_maxFVars_x3f_340_, lean_object* v_k_341_, uint8_t v_cleanupAnnotations_342_, uint8_t v_whnfType_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; 
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_349_, 0, v_k_341_);
v___x_350_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_339_, v_maxFVars_x3f_340_, v___f_349_, v_cleanupAnnotations_342_, v_whnfType_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_350_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_350_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_339_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_340_ = stack[1].m_obj;
lean_object* v_k_341_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_342_ = stack[3].m_num;
uint8_t v_whnfType_343_ = stack[4].m_num;
lean_object* v___y_344_ = stack[5].m_obj;
lean_object* v___y_345_ = stack[6].m_obj;
lean_object* v___y_346_ = stack[7].m_obj;
lean_object* v___y_347_ = stack[8].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_339_, v_maxFVars_x3f_340_, v_k_341_, v_cleanupAnnotations_342_, v_whnfType_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg___boxed(lean_object* v_type_368_, lean_object* v_maxFVars_x3f_369_, lean_object* v_k_370_, lean_object* v_cleanupAnnotations_371_, lean_object* v_whnfType_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_378_; uint8_t v_whnfType_boxed_379_; lean_object* v_res_380_; 
v_cleanupAnnotations_boxed_378_ = lean_unbox(v_cleanupAnnotations_371_);
v_whnfType_boxed_379_ = lean_unbox(v_whnfType_372_);
v_res_380_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_368_, v_maxFVars_x3f_369_, v_k_370_, v_cleanupAnnotations_boxed_378_, v_whnfType_boxed_379_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_380_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(lean_object* v_00_u03b1_381_, lean_object* v_type_382_, lean_object* v_maxFVars_x3f_383_, lean_object* v_k_384_, uint8_t v_cleanupAnnotations_385_, uint8_t v_whnfType_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_382_, v_maxFVars_x3f_383_, v_k_384_, v_cleanupAnnotations_385_, v_whnfType_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_392_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_382_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_383_ = stack[2].m_obj;
lean_object* v_k_384_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_385_ = stack[4].m_num;
uint8_t v_whnfType_386_ = stack[5].m_num;
lean_object* v___y_387_ = stack[6].m_obj;
lean_object* v___y_388_ = stack[7].m_obj;
lean_object* v___y_389_ = stack[8].m_obj;
lean_object* v___y_390_ = stack[9].m_obj;
lean_object* v_res_393_;
v_res_393_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(lean_box(0), v_type_382_, v_maxFVars_x3f_383_, v_k_384_, v_cleanupAnnotations_385_, v_whnfType_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___boxed(lean_object* v_00_u03b1_394_, lean_object* v_type_395_, lean_object* v_maxFVars_x3f_396_, lean_object* v_k_397_, lean_object* v_cleanupAnnotations_398_, lean_object* v_whnfType_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_405_; uint8_t v_whnfType_boxed_406_; lean_object* v_res_407_; 
v_cleanupAnnotations_boxed_405_ = lean_unbox(v_cleanupAnnotations_398_);
v_whnfType_boxed_406_ = lean_unbox(v_whnfType_399_);
v_res_407_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2(v_00_u03b1_394_, v_type_395_, v_maxFVars_x3f_396_, v_k_397_, v_cleanupAnnotations_boxed_405_, v_whnfType_boxed_406_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_407_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(lean_object* v___x_408_, lean_object* v_type_409_, uint8_t v___x_410_, uint8_t v___x_411_, lean_object* v_tuple_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_inc_ref(v_tuple_412_);
v___x_418_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_mkTupleElems(v_tuple_412_, v___x_408_);
v___x_419_ = l_Lean_Meta_instantiateForall(v_type_409_, v___x_418_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec_ref(v___x_418_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_mk_empty_array_with_capacity(v___x_421_);
v___x_423_ = lean_array_push(v___x_422_, v_tuple_412_);
v___x_424_ = 1;
v___x_425_ = l_Lean_Meta_mkForallFVars(v___x_423_, v_a_420_, v___x_410_, v___x_411_, v___x_411_, v___x_424_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec_ref(v___x_423_);
return v___x_425_;
}
else
{
lean_dec_ref(v_tuple_412_);
return v___x_419_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_408_ = stack[0].m_obj;
lean_object* v_type_409_ = stack[1].m_obj;
uint8_t v___x_410_ = stack[2].m_num;
uint8_t v___x_411_ = stack[3].m_num;
lean_object* v_tuple_412_ = stack[4].m_obj;
lean_object* v___y_413_ = stack[5].m_obj;
lean_object* v___y_414_ = stack[6].m_obj;
lean_object* v___y_415_ = stack[7].m_obj;
lean_object* v___y_416_ = stack[8].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(v___x_408_, v_type_409_, v___x_410_, v___x_411_, v_tuple_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed(lean_object* v___x_427_, lean_object* v_type_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v_tuple_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
uint8_t v___x_1322__boxed_437_; uint8_t v___x_1323__boxed_438_; lean_object* v_res_439_; 
v___x_1322__boxed_437_ = lean_unbox(v___x_429_);
v___x_1323__boxed_438_ = lean_unbox(v___x_430_);
v_res_439_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0(v___x_427_, v_type_428_, v___x_1322__boxed_437_, v___x_1323__boxed_438_, v_tuple_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___x_427_);
return v_res_439_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(lean_object* v_k_440_, lean_object* v_b_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
v___x_447_ = lean_apply_6(v_k_440_, v_b_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, lean_box(0));
return v___x_447_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_440_ = stack[0].m_obj;
lean_object* v_b_441_ = stack[1].m_obj;
lean_object* v___y_442_ = stack[2].m_obj;
lean_object* v___y_443_ = stack[3].m_obj;
lean_object* v___y_444_ = stack[4].m_obj;
lean_object* v___y_445_ = stack[5].m_obj;
lean_object* v_res_448_;
v_res_448_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(v_k_440_, v_b_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_449_, lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0(v_k_449_, v_b_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(lean_object* v_name_457_, uint8_t v_bi_458_, lean_object* v_type_459_, lean_object* v_k_460_, uint8_t v_kind_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___f_467_; lean_object* v___x_468_; 
v___f_467_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_467_, 0, v_k_460_);
v___x_468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_457_, v_bi_458_, v_type_459_, v___f_467_, v_kind_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
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
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_468_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_468_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_457_ = stack[0].m_obj;
uint8_t v_bi_458_ = stack[1].m_num;
lean_object* v_type_459_ = stack[2].m_obj;
lean_object* v_k_460_ = stack[3].m_obj;
uint8_t v_kind_461_ = stack[4].m_num;
lean_object* v___y_462_ = stack[5].m_obj;
lean_object* v___y_463_ = stack[6].m_obj;
lean_object* v___y_464_ = stack[7].m_obj;
lean_object* v___y_465_ = stack[8].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_457_, v_bi_458_, v_type_459_, v_k_460_, v_kind_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg___boxed(lean_object* v_name_486_, lean_object* v_bi_487_, lean_object* v_type_488_, lean_object* v_k_489_, lean_object* v_kind_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
uint8_t v_bi_boxed_496_; uint8_t v_kind_boxed_497_; lean_object* v_res_498_; 
v_bi_boxed_496_ = lean_unbox(v_bi_487_);
v_kind_boxed_497_ = lean_unbox(v_kind_490_);
v_res_498_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_486_, v_bi_boxed_496_, v_type_488_, v_k_489_, v_kind_boxed_497_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_498_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(lean_object* v_name_499_, lean_object* v_type_500_, lean_object* v_k_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; 
v___x_507_ = 0;
v___x_508_ = 0;
v___x_509_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_499_, v___x_507_, v_type_500_, v_k_501_, v___x_508_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_509_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_499_ = stack[0].m_obj;
lean_object* v_type_500_ = stack[1].m_obj;
lean_object* v_k_501_ = stack[2].m_obj;
lean_object* v___y_502_ = stack[3].m_obj;
lean_object* v___y_503_ = stack[4].m_obj;
lean_object* v___y_504_ = stack[5].m_obj;
lean_object* v___y_505_ = stack[6].m_obj;
lean_object* v_res_510_;
v_res_510_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_499_, v_type_500_, v_k_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg___boxed(lean_object* v_name_511_, lean_object* v_type_512_, lean_object* v_k_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_511_, v_type_512_, v_k_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_519_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_522_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__1));
v___x_523_ = lean_unsigned_to_nat(6u);
v___x_524_ = lean_unsigned_to_nat(138u);
v___x_525_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__0));
v___x_526_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_527_ = l_mkPanicMessageWithDecl(v___x_526_, v___x_525_, v___x_524_, v___x_523_, v___x_522_);
return v___x_527_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(lean_object* v___x_531_, lean_object* v_type_532_, uint8_t v___x_533_, uint8_t v___x_534_, lean_object* v___x_535_, lean_object* v_varNames_536_, lean_object* v___x_537_, lean_object* v_xs_538_, lean_object* v_x_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_array_get_size(v_xs_538_);
v___x_546_ = lean_nat_dec_eq(v___x_545_, v___x_531_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref(v_xs_538_);
lean_dec_ref(v_type_532_);
v___x_547_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__2);
v___x_548_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_547_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___f_551_; lean_object* v___x_552_; 
v___x_549_ = lean_box(v___x_533_);
v___x_550_ = lean_box(v___x_534_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__0___boxed), 10, 4);
lean_closure_set(v___f_551_, 0, v___x_545_);
lean_closure_set(v___f_551_, 1, v_type_532_);
lean_closure_set(v___f_551_, 2, v___x_549_);
lean_closure_set(v___f_551_, 3, v___x_550_);
v___x_552_ = l_Lean_Meta_ArgsPacker_Unary_packType(v_xs_538_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_dec_eq(v___x_545_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_557_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_556_, v_a_553_, v___f_551_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_array_get_borrowed(v___x_535_, v_varNames_536_, v___x_537_);
lean_inc(v___x_558_);
v___x_559_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_558_, v_a_553_, v___f_551_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_559_;
}
}
else
{
lean_dec_ref(v___f_551_);
return v___x_552_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_531_ = stack[0].m_obj;
lean_object* v_type_532_ = stack[1].m_obj;
uint8_t v___x_533_ = stack[2].m_num;
uint8_t v___x_534_ = stack[3].m_num;
lean_object* v___x_535_ = stack[4].m_obj;
lean_object* v_varNames_536_ = stack[5].m_obj;
lean_object* v___x_537_ = stack[6].m_obj;
lean_object* v_xs_538_ = stack[7].m_obj;
lean_object* v_x_539_ = stack[8].m_obj;
lean_object* v___y_540_ = stack[9].m_obj;
lean_object* v___y_541_ = stack[10].m_obj;
lean_object* v___y_542_ = stack[11].m_obj;
lean_object* v___y_543_ = stack[12].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(v___x_531_, v_type_532_, v___x_533_, v___x_534_, v___x_535_, v_varNames_536_, v___x_537_, v_xs_538_, v_x_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed(lean_object* v___x_561_, lean_object* v_type_562_, lean_object* v___x_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v_varNames_566_, lean_object* v___x_567_, lean_object* v_xs_568_, lean_object* v_x_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
uint8_t v___x_1551__boxed_575_; uint8_t v___x_1552__boxed_576_; lean_object* v_res_577_; 
v___x_1551__boxed_575_ = lean_unbox(v___x_563_);
v___x_1552__boxed_576_ = lean_unbox(v___x_564_);
v_res_577_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1(v___x_561_, v_type_562_, v___x_1551__boxed_575_, v___x_1552__boxed_576_, v___x_565_, v_varNames_566_, v___x_567_, v_xs_568_, v_x_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v_x_569_);
lean_dec(v___x_567_);
lean_dec_ref(v_varNames_566_);
lean_dec(v___x_565_);
lean_dec(v___x_561_);
return v_res_577_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType(lean_object* v_varNames_578_, lean_object* v_type_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_array_get_size(v_varNames_578_);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_nat_dec_eq(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_588_ = lean_box(0);
v___x_589_ = 1;
v___x_590_ = lean_box(v___x_587_);
v___x_591_ = lean_box(v___x_589_);
lean_inc_ref(v_type_579_);
v___f_592_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___boxed), 14, 7);
lean_closure_set(v___f_592_, 0, v___x_585_);
lean_closure_set(v___f_592_, 1, v_type_579_);
lean_closure_set(v___f_592_, 2, v___x_590_);
lean_closure_set(v___f_592_, 3, v___x_591_);
lean_closure_set(v___f_592_, 4, v___x_588_);
lean_closure_set(v___f_592_, 5, v_varNames_578_);
lean_closure_set(v___f_592_, 6, v___x_586_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_585_);
v___x_594_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_type_579_, v___x_593_, v___f_592_, v___x_587_, v___x_587_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref(v_varNames_578_);
v___x_595_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_596_ = l_Lean_mkArrow(v___x_595_, v_type_579_, v_a_582_, v_a_583_);
return v___x_596_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Unary_uncurryType_0interp(lean_interpreter_value* stack)
{
lean_object* v_varNames_578_ = stack[0].m_obj;
lean_object* v_type_579_ = stack[1].m_obj;
lean_object* v_a_580_ = stack[2].m_obj;
lean_object* v_a_581_ = stack[3].m_obj;
lean_object* v_a_582_ = stack[4].m_obj;
lean_object* v_a_583_ = stack[5].m_obj;
lean_object* v_res_597_;
v_res_597_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_578_, v_type_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
stack->m_obj
 = v_res_597_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurryType___boxed(lean_object* v_varNames_598_, lean_object* v_type_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_598_, v_type_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
return v_res_605_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(lean_object* v_00_u03b1_606_, lean_object* v_name_607_, uint8_t v_bi_608_, lean_object* v_type_609_, lean_object* v_k_610_, uint8_t v_kind_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___redArg(v_name_607_, v_bi_608_, v_type_609_, v_k_610_, v_kind_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_617_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_607_ = stack[1].m_obj;
uint8_t v_bi_608_ = stack[2].m_num;
lean_object* v_type_609_ = stack[3].m_obj;
lean_object* v_k_610_ = stack[4].m_obj;
uint8_t v_kind_611_ = stack[5].m_num;
lean_object* v___y_612_ = stack[6].m_obj;
lean_object* v___y_613_ = stack[7].m_obj;
lean_object* v___y_614_ = stack[8].m_obj;
lean_object* v___y_615_ = stack[9].m_obj;
lean_object* v_res_618_;
v_res_618_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(lean_box(0), v_name_607_, v_bi_608_, v_type_609_, v_k_610_, v_kind_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
stack->m_obj
 = v_res_618_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1___boxed(lean_object* v_00_u03b1_619_, lean_object* v_name_620_, lean_object* v_bi_621_, lean_object* v_type_622_, lean_object* v_k_623_, lean_object* v_kind_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
uint8_t v_bi_boxed_630_; uint8_t v_kind_boxed_631_; lean_object* v_res_632_; 
v_bi_boxed_630_ = lean_unbox(v_bi_621_);
v_kind_boxed_631_ = lean_unbox(v_kind_624_);
v_res_632_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_spec__1(v_00_u03b1_619_, v_name_620_, v_bi_boxed_630_, v_type_622_, v_k_623_, v_kind_boxed_631_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
return v_res_632_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(lean_object* v_00_u03b1_633_, lean_object* v_name_634_, lean_object* v_type_635_, lean_object* v_k_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_634_, v_type_635_, v_k_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
return v___x_642_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_634_ = stack[1].m_obj;
lean_object* v_type_635_ = stack[2].m_obj;
lean_object* v_k_636_ = stack[3].m_obj;
lean_object* v___y_637_ = stack[4].m_obj;
lean_object* v___y_638_ = stack[5].m_obj;
lean_object* v___y_639_ = stack[6].m_obj;
lean_object* v___y_640_ = stack[7].m_obj;
lean_object* v_res_643_;
v_res_643_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(lean_box(0), v_name_634_, v_type_635_, v_k_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___boxed(lean_object* v_00_u03b1_644_, lean_object* v_name_645_, lean_object* v_type_646_, lean_object* v_k_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1(v_00_u03b1_644_, v_name_645_, v_type_646_, v_k_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
return v_res_653_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(lean_object* v_msgData_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_env_661_; uint8_t v___x_662_; lean_object* v_env_663_; lean_object* v___x_664_; lean_object* v_toCold_665_; lean_object* v_mctx_666_; lean_object* v_lctx_667_; lean_object* v_options_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_660_ = lean_st_ref_get(v___y_658_);
v_env_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc_ref(v_env_661_);
lean_dec(v___x_660_);
v___x_662_ = 0;
v_env_663_ = l_Lean_Environment_setRecordingDeps(v_env_661_, v___x_662_);
v___x_664_ = lean_st_ref_get(v___y_656_);
v_toCold_665_ = lean_ctor_get(v___y_657_, 0);
v_mctx_666_ = lean_ctor_get(v___x_664_, 0);
lean_inc_ref(v_mctx_666_);
lean_dec(v___x_664_);
v_lctx_667_ = lean_ctor_get(v___y_655_, 2);
v_options_668_ = lean_ctor_get(v_toCold_665_, 2);
lean_inc_ref(v_options_668_);
lean_inc_ref(v_lctx_667_);
v___x_669_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_669_, 0, v_env_663_);
lean_ctor_set(v___x_669_, 1, v_mctx_666_);
lean_ctor_set(v___x_669_, 2, v_lctx_667_);
lean_ctor_set(v___x_669_, 3, v_options_668_);
v___x_670_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v_msgData_654_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_654_ = stack[0].m_obj;
lean_object* v___y_655_ = stack[1].m_obj;
lean_object* v___y_656_ = stack[2].m_obj;
lean_object* v___y_657_ = stack[3].m_obj;
lean_object* v___y_658_ = stack[4].m_obj;
lean_object* v_res_672_;
v_res_672_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msgData_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
stack->m_obj
 = v_res_672_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0___boxed(lean_object* v_msgData_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msgData_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_679_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_ref_686_; lean_object* v___x_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
v_ref_686_ = lean_ctor_get(v___y_683_, 2);
v___x_687_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_spec__0(v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
lean_inc(v_ref_686_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_ref_686_);
lean_ctor_set(v___x_692_, 1, v_a_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 1);
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_680_ = stack[0].m_obj;
lean_object* v___y_681_ = stack[1].m_obj;
lean_object* v___y_682_ = stack[2].m_obj;
lean_object* v___y_683_ = stack[3].m_obj;
lean_object* v___y_684_ = stack[4].m_obj;
lean_object* v_res_697_;
v_res_697_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
stack->m_obj
 = v_res_697_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg___boxed(lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__0));
v___x_707_ = l_Lean_stringToMessageData(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed(lean_object** _args){
lean_object* v___x_708_ = _args[0];
lean_object* v___x_709_ = _args[1];
lean_object* v___x_710_ = _args[2];
lean_object* v_arg_711_ = _args[3];
lean_object* v_arg_712_ = _args[4];
lean_object* v_a_713_ = _args[5];
lean_object* v_alt_714_ = _args[6];
lean_object* v_tail_715_ = _args[7];
lean_object* v_u_716_ = _args[8];
lean_object* v___x_717_ = _args[9];
lean_object* v___x_718_ = _args[10];
lean_object* v___x_719_ = _args[11];
lean_object* v_head_720_ = _args[12];
lean_object* v_x_721_ = _args[13];
lean_object* v___y_722_ = _args[14];
lean_object* v___y_723_ = _args[15];
lean_object* v___y_724_ = _args[16];
lean_object* v___y_725_ = _args[17];
lean_object* v___y_726_ = _args[18];
_start:
{
uint8_t v___x_2898__boxed_727_; uint8_t v___x_2899__boxed_728_; uint8_t v___x_2900__boxed_729_; lean_object* v_res_730_; 
v___x_2898__boxed_727_ = lean_unbox(v___x_717_);
v___x_2899__boxed_728_ = lean_unbox(v___x_718_);
v___x_2900__boxed_729_ = lean_unbox(v___x_719_);
v_res_730_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(v___x_708_, v___x_709_, v___x_710_, v_arg_711_, v_arg_712_, v_a_713_, v_alt_714_, v_tail_715_, v_u_716_, v___x_2898__boxed_727_, v___x_2899__boxed_728_, v___x_2900__boxed_729_, v_head_720_, v_x_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_730_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(lean_object* v_varNames_735_, lean_object* v_e_736_, lean_object* v_u_737_, lean_object* v_codomain_738_, lean_object* v_alt_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
if (lean_obj_tag(v_varNames_735_) == 0)
{
lean_object* v___x_745_; 
lean_dec_ref(v_codomain_738_);
lean_dec(v_u_737_);
lean_dec_ref(v_e_736_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_alt_739_);
return v___x_745_;
}
else
{
lean_object* v_tail_746_; 
v_tail_746_ = lean_ctor_get(v_varNames_735_, 1);
lean_inc(v_tail_746_);
if (lean_obj_tag(v_tail_746_) == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref_known(v_varNames_735_, 2);
lean_dec_ref(v_codomain_738_);
lean_dec(v_u_737_);
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_mk_empty_array_with_capacity(v___x_747_);
v___x_749_ = lean_array_push(v___x_748_, v_e_736_);
v___x_750_ = l_Lean_Expr_beta(v_alt_739_, v___x_749_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
else
{
lean_object* v_head_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_808_; 
v_head_752_ = lean_ctor_get(v_varNames_735_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v_varNames_735_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_varNames_735_, 1);
lean_dec(v_unused_809_);
v___x_754_ = v_varNames_735_;
v_isShared_755_ = v_isSharedCheck_808_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_head_752_);
lean_dec(v_varNames_735_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_808_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_head_756_; lean_object* v___x_757_; 
v_head_756_ = lean_ctor_get(v_tail_746_, 0);
lean_inc(v_head_756_);
lean_inc(v_a_743_);
lean_inc_ref(v_a_742_);
lean_inc(v_a_741_);
lean_inc_ref(v_a_740_);
lean_inc_ref(v_e_736_);
v___x_757_ = lean_infer_type(v_e_736_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___x_768_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc_n(v_a_758_, 2);
lean_dec_ref_known(v___x_757_, 1);
v___x_768_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_758_, v_a_741_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_Lean_Expr_cleanupAnnotations(v_a_769_);
v___x_771_ = l_Lean_Expr_isApp(v___x_770_);
if (v___x_771_ == 0)
{
lean_dec_ref(v___x_770_);
lean_dec(v_head_756_);
lean_del_object(v___x_754_);
lean_dec(v_head_752_);
lean_dec_ref_known(v_tail_746_, 2);
lean_dec_ref(v_alt_739_);
lean_dec_ref(v_codomain_738_);
lean_dec(v_u_737_);
lean_dec_ref(v_e_736_);
v___y_760_ = v_a_740_;
v___y_761_ = v_a_741_;
v___y_762_ = v_a_742_;
v___y_763_ = v_a_743_;
goto v___jp_759_;
}
else
{
lean_object* v_arg_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_arg_772_ = lean_ctor_get(v___x_770_, 1);
lean_inc_ref(v_arg_772_);
v___x_773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_770_);
v___x_774_ = l_Lean_Expr_isApp(v___x_773_);
if (v___x_774_ == 0)
{
lean_dec_ref(v___x_773_);
lean_dec_ref(v_arg_772_);
lean_dec(v_head_756_);
lean_del_object(v___x_754_);
lean_dec_ref_known(v_tail_746_, 2);
lean_dec(v_head_752_);
lean_dec_ref(v_alt_739_);
lean_dec_ref(v_codomain_738_);
lean_dec(v_u_737_);
lean_dec_ref(v_e_736_);
v___y_760_ = v_a_740_;
v___y_761_ = v_a_741_;
v___y_762_ = v_a_742_;
v___y_763_ = v_a_743_;
goto v___jp_759_;
}
else
{
lean_object* v_arg_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_arg_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc_ref(v_arg_775_);
v___x_776_ = l_Lean_Expr_appFnCleanup___redArg(v___x_773_);
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0));
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_779_ = l_Lean_Expr_isConstOf(v___x_776_, v___x_778_);
lean_dec_ref(v___x_776_);
if (v___x_779_ == 0)
{
lean_dec_ref(v_arg_775_);
lean_dec_ref(v_arg_772_);
lean_dec(v_head_756_);
lean_del_object(v___x_754_);
lean_dec_ref_known(v_tail_746_, 2);
lean_dec(v_head_752_);
lean_dec_ref(v_alt_739_);
lean_dec_ref(v_codomain_738_);
lean_dec(v_u_737_);
lean_dec_ref(v_e_736_);
v___y_760_ = v_a_740_;
v___y_761_ = v_a_741_;
v___y_762_ = v_a_742_;
v___y_763_ = v_a_743_;
goto v___jp_759_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v___x_780_ = l_Lean_Expr_getAppFn(v_a_758_);
lean_dec(v_a_758_);
v___x_781_ = l_Lean_Expr_constLevels_x21(v___x_780_);
lean_dec_ref(v___x_780_);
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_mk_empty_array_with_capacity(v___x_782_);
lean_inc_ref(v_e_736_);
lean_inc_ref(v___x_783_);
v___x_784_ = lean_array_push(v___x_783_, v_e_736_);
v___x_785_ = 0;
v___x_786_ = 1;
v___x_787_ = l_Lean_Meta_mkLambdaFVars(v___x_784_, v_codomain_738_, v___x_785_, v___x_779_, v___x_785_, v___x_779_, v___x_786_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec_ref(v___x_784_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___f_792_; lean_object* v___x_793_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_n(v_a_788_, 2);
lean_dec_ref_known(v___x_787_, 1);
v___x_789_ = lean_box(v___x_785_);
v___x_790_ = lean_box(v___x_779_);
v___x_791_ = lean_box(v___x_786_);
lean_inc(v_u_737_);
lean_inc_ref(v_arg_772_);
lean_inc_ref_n(v_arg_775_, 2);
lean_inc(v___x_781_);
v___f_792_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed), 19, 13);
lean_closure_set(v___f_792_, 0, v___x_783_);
lean_closure_set(v___f_792_, 1, v___x_777_);
lean_closure_set(v___f_792_, 2, v___x_781_);
lean_closure_set(v___f_792_, 3, v_arg_775_);
lean_closure_set(v___f_792_, 4, v_arg_772_);
lean_closure_set(v___f_792_, 5, v_a_788_);
lean_closure_set(v___f_792_, 6, v_alt_739_);
lean_closure_set(v___f_792_, 7, v_tail_746_);
lean_closure_set(v___f_792_, 8, v_u_737_);
lean_closure_set(v___f_792_, 9, v___x_789_);
lean_closure_set(v___f_792_, 10, v___x_790_);
lean_closure_set(v___f_792_, 11, v___x_791_);
lean_closure_set(v___f_792_, 12, v_head_756_);
v___x_793_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_752_, v_arg_775_, v___f_792_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_807_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_807_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_807_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_807_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__3));
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_781_);
lean_ctor_set(v___x_754_, 0, v_u_737_);
v___x_800_ = v___x_754_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_u_737_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_781_);
v___x_800_ = v_reuseFailAlloc_806_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_801_ = l_Lean_Expr_const___override(v___x_798_, v___x_800_);
v___x_802_ = l_Lean_mkApp5(v___x_801_, v_arg_775_, v_arg_772_, v_a_788_, v_e_736_, v_a_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_802_);
v___x_804_ = v___x_796_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_dec(v_a_788_);
lean_dec(v___x_781_);
lean_dec_ref(v_arg_775_);
lean_dec_ref(v_arg_772_);
lean_del_object(v___x_754_);
lean_dec(v_u_737_);
lean_dec_ref(v_e_736_);
return v___x_793_;
}
}
else
{
lean_dec_ref(v___x_783_);
lean_dec(v___x_781_);
lean_dec_ref(v_arg_775_);
lean_dec_ref(v_arg_772_);
lean_dec(v_head_756_);
lean_del_object(v___x_754_);
lean_dec(v_head_752_);
lean_dec_ref_known(v_tail_746_, 2);
lean_dec_ref(v_alt_739_);
lean_dec(v_u_737_);
lean_dec_ref(v_e_736_);
return v___x_787_;
}
}
}
}
}
else
{
lean_dec(v_a_758_);
lean_dec(v_head_756_);
lean_del_object(v___x_754_);
lean_dec(v_head_752_);
lean_dec_ref_known(v_tail_746_, 2);
lean_dec_ref(v_alt_739_);
lean_dec_ref(v_codomain_738_);
lean_dec(v_u_737_);
lean_dec_ref(v_e_736_);
return v___x_768_;
}
v___jp_759_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__1);
v___x_765_ = l_Lean_MessageData_ofExpr(v_a_758_);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_766_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
return v___x_767_;
}
}
else
{
lean_dec(v_head_756_);
lean_del_object(v___x_754_);
lean_dec_ref_known(v_tail_746_, 2);
lean_dec(v_head_752_);
lean_dec_ref(v_alt_739_);
lean_dec_ref(v_codomain_738_);
lean_dec(v_u_737_);
lean_dec_ref(v_e_736_);
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_varNames_735_ = stack[0].m_obj;
lean_object* v_e_736_ = stack[1].m_obj;
lean_object* v_u_737_ = stack[2].m_obj;
lean_object* v_codomain_738_ = stack[3].m_obj;
lean_object* v_alt_739_ = stack[4].m_obj;
lean_object* v_a_740_ = stack[5].m_obj;
lean_object* v_a_741_ = stack[6].m_obj;
lean_object* v_a_742_ = stack[7].m_obj;
lean_object* v_a_743_ = stack[8].m_obj;
lean_object* v_res_810_;
v_res_810_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_varNames_735_, v_e_736_, v_u_737_, v_codomain_738_, v_alt_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
stack->m_obj
 = v_res_810_;
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v_arg_813_, lean_object* v_arg_814_, lean_object* v_x_815_, lean_object* v___x_816_, lean_object* v_a_817_, lean_object* v_alt_818_, lean_object* v___x_819_, lean_object* v_tail_820_, lean_object* v_u_821_, uint8_t v___x_822_, uint8_t v___x_823_, uint8_t v___x_824_, lean_object* v_y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__6));
v___x_832_ = l_Lean_Name_mkStr2(v___x_811_, v___x_831_);
v___x_833_ = l_Lean_Expr_const___override(v___x_832_, v___x_812_);
lean_inc_ref_n(v_y_825_, 2);
lean_inc_ref(v_x_815_);
v___x_834_ = l_Lean_mkApp4(v___x_833_, v_arg_813_, v_arg_814_, v_x_815_, v_y_825_);
v___x_835_ = lean_array_push(v___x_816_, v___x_834_);
v___x_836_ = l_Lean_Expr_beta(v_a_817_, v___x_835_);
v___x_837_ = l_Lean_Expr_beta(v_alt_818_, v___x_819_);
v___x_838_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_tail_820_, v_y_825_, v_u_821_, v___x_836_, v___x_837_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v___x_840_ = lean_unsigned_to_nat(2u);
v___x_841_ = lean_mk_empty_array_with_capacity(v___x_840_);
v___x_842_ = lean_array_push(v___x_841_, v_x_815_);
v___x_843_ = lean_array_push(v___x_842_, v_y_825_);
v___x_844_ = l_Lean_Meta_mkLambdaFVars(v___x_843_, v_a_839_, v___x_822_, v___x_823_, v___x_822_, v___x_823_, v___x_824_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec_ref(v___x_843_);
return v___x_844_;
}
else
{
lean_dec_ref(v_y_825_);
lean_dec_ref(v_x_815_);
return v___x_838_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_811_ = stack[0].m_obj;
lean_object* v___x_812_ = stack[1].m_obj;
lean_object* v_arg_813_ = stack[2].m_obj;
lean_object* v_arg_814_ = stack[3].m_obj;
lean_object* v_x_815_ = stack[4].m_obj;
lean_object* v___x_816_ = stack[5].m_obj;
lean_object* v_a_817_ = stack[6].m_obj;
lean_object* v_alt_818_ = stack[7].m_obj;
lean_object* v___x_819_ = stack[8].m_obj;
lean_object* v_tail_820_ = stack[9].m_obj;
lean_object* v_u_821_ = stack[10].m_obj;
uint8_t v___x_822_ = stack[11].m_num;
uint8_t v___x_823_ = stack[12].m_num;
uint8_t v___x_824_ = stack[13].m_num;
lean_object* v_y_825_ = stack[14].m_obj;
lean_object* v___y_826_ = stack[15].m_obj;
lean_object* v___y_827_ = stack[16].m_obj;
lean_object* v___y_828_ = stack[17].m_obj;
lean_object* v___y_829_ = stack[18].m_obj;
lean_object* v_res_845_;
v_res_845_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(v___x_811_, v___x_812_, v_arg_813_, v_arg_814_, v_x_815_, v___x_816_, v_a_817_, v_alt_818_, v___x_819_, v_tail_820_, v_u_821_, v___x_822_, v___x_823_, v___x_824_, v_y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
stack->m_obj
 = v_res_845_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_846_ = _args[0];
lean_object* v___x_847_ = _args[1];
lean_object* v_arg_848_ = _args[2];
lean_object* v_arg_849_ = _args[3];
lean_object* v_x_850_ = _args[4];
lean_object* v___x_851_ = _args[5];
lean_object* v_a_852_ = _args[6];
lean_object* v_alt_853_ = _args[7];
lean_object* v___x_854_ = _args[8];
lean_object* v_tail_855_ = _args[9];
lean_object* v_u_856_ = _args[10];
lean_object* v___x_857_ = _args[11];
lean_object* v___x_858_ = _args[12];
lean_object* v___x_859_ = _args[13];
lean_object* v_y_860_ = _args[14];
lean_object* v___y_861_ = _args[15];
lean_object* v___y_862_ = _args[16];
lean_object* v___y_863_ = _args[17];
lean_object* v___y_864_ = _args[18];
lean_object* v___y_865_ = _args[19];
_start:
{
uint8_t v___x_2919__boxed_866_; uint8_t v___x_2920__boxed_867_; uint8_t v___x_2921__boxed_868_; lean_object* v_res_869_; 
v___x_2919__boxed_866_ = lean_unbox(v___x_857_);
v___x_2920__boxed_867_ = lean_unbox(v___x_858_);
v___x_2921__boxed_868_ = lean_unbox(v___x_859_);
v_res_869_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(v___x_846_, v___x_847_, v_arg_848_, v_arg_849_, v_x_850_, v___x_851_, v_a_852_, v_alt_853_, v___x_854_, v_tail_855_, v_u_856_, v___x_2919__boxed_866_, v___x_2920__boxed_867_, v___x_2921__boxed_868_, v_y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_869_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v_arg_873_, lean_object* v_arg_874_, lean_object* v_a_875_, lean_object* v_alt_876_, lean_object* v_tail_877_, lean_object* v_u_878_, uint8_t v___x_879_, uint8_t v___x_880_, uint8_t v___x_881_, lean_object* v_head_882_, lean_object* v_x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc_ref(v_x_883_);
lean_inc_ref(v___x_870_);
v___x_889_ = lean_array_push(v___x_870_, v_x_883_);
v___x_890_ = lean_box(v___x_879_);
v___x_891_ = lean_box(v___x_880_);
v___x_892_ = lean_box(v___x_881_);
lean_inc_ref(v___x_889_);
lean_inc_ref(v_arg_874_);
v___f_893_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0___boxed), 20, 14);
lean_closure_set(v___f_893_, 0, v___x_871_);
lean_closure_set(v___f_893_, 1, v___x_872_);
lean_closure_set(v___f_893_, 2, v_arg_873_);
lean_closure_set(v___f_893_, 3, v_arg_874_);
lean_closure_set(v___f_893_, 4, v_x_883_);
lean_closure_set(v___f_893_, 5, v___x_870_);
lean_closure_set(v___f_893_, 6, v_a_875_);
lean_closure_set(v___f_893_, 7, v_alt_876_);
lean_closure_set(v___f_893_, 8, v___x_889_);
lean_closure_set(v___f_893_, 9, v_tail_877_);
lean_closure_set(v___f_893_, 10, v_u_878_);
lean_closure_set(v___f_893_, 11, v___x_890_);
lean_closure_set(v___f_893_, 12, v___x_891_);
lean_closure_set(v___f_893_, 13, v___x_892_);
v___x_894_ = l_Lean_Expr_beta(v_arg_874_, v___x_889_);
v___x_895_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_882_, v___x_894_, v___f_893_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_895_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_870_ = stack[0].m_obj;
lean_object* v___x_871_ = stack[1].m_obj;
lean_object* v___x_872_ = stack[2].m_obj;
lean_object* v_arg_873_ = stack[3].m_obj;
lean_object* v_arg_874_ = stack[4].m_obj;
lean_object* v_a_875_ = stack[5].m_obj;
lean_object* v_alt_876_ = stack[6].m_obj;
lean_object* v_tail_877_ = stack[7].m_obj;
lean_object* v_u_878_ = stack[8].m_obj;
uint8_t v___x_879_ = stack[9].m_num;
uint8_t v___x_880_ = stack[10].m_num;
uint8_t v___x_881_ = stack[11].m_num;
lean_object* v_head_882_ = stack[12].m_obj;
lean_object* v_x_883_ = stack[13].m_obj;
lean_object* v___y_884_ = stack[14].m_obj;
lean_object* v___y_885_ = stack[15].m_obj;
lean_object* v___y_886_ = stack[16].m_obj;
lean_object* v___y_887_ = stack[17].m_obj;
lean_object* v_res_896_;
v_res_896_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(v___x_870_, v___x_871_, v___x_872_, v_arg_873_, v_arg_874_, v_a_875_, v_alt_876_, v_tail_877_, v_u_878_, v___x_879_, v___x_880_, v___x_881_, v_head_882_, v_x_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___boxed(lean_object* v_varNames_897_, lean_object* v_e_898_, lean_object* v_u_899_, lean_object* v_codomain_900_, lean_object* v_alt_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v_varNames_897_, v_e_898_, v_u_899_, v_codomain_900_, v_alt_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
return v_res_907_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(lean_object* v_00_u03b1_908_, lean_object* v_msg_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v_msg_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
return v___x_915_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_909_ = stack[1].m_obj;
lean_object* v___y_910_ = stack[2].m_obj;
lean_object* v___y_911_ = stack[3].m_obj;
lean_object* v___y_912_ = stack[4].m_obj;
lean_object* v___y_913_ = stack[5].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(lean_box(0), v_msg_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___boxed(lean_object* v_00_u03b1_917_, lean_object* v_msg_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0(v_00_u03b1_917_, v_msg_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_924_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_927_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_928_ = lean_unsigned_to_nat(23u);
v___x_929_ = lean_unsigned_to_nat(180u);
v___x_930_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__0));
v___x_931_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_932_ = l_mkPanicMessageWithDecl(v___x_931_, v___x_930_, v___x_929_, v___x_928_, v___x_927_);
return v___x_932_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v_varNames_935_, lean_object* v_e_936_, uint8_t v___x_937_, uint8_t v___x_938_, lean_object* v_xs_939_, lean_object* v_codomain_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_array_get_size(v_xs_939_);
v___x_947_ = lean_nat_dec_eq(v___x_946_, v___x_933_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec_ref(v_codomain_940_);
lean_dec_ref(v_e_936_);
lean_dec_ref(v_varNames_935_);
v___x_948_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2, &l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__2);
v___x_949_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_948_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_array_fget_borrowed(v_xs_939_, v___x_934_);
lean_inc_ref(v_codomain_940_);
v___x_951_ = l_Lean_Meta_getLevel(v_codomain_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_array_to_list(v_varNames_935_);
lean_inc(v___x_950_);
v___x_954_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn(v___x_953_, v___x_950_, v_a_952_, v_codomain_940_, v_e_936_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = lean_mk_empty_array_with_capacity(v___x_933_);
lean_inc(v___x_950_);
v___x_957_ = lean_array_push(v___x_956_, v___x_950_);
v___x_958_ = 1;
v___x_959_ = l_Lean_Meta_mkLambdaFVars(v___x_957_, v_a_955_, v___x_937_, v___x_938_, v___x_937_, v___x_938_, v___x_958_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec_ref(v___x_957_);
return v___x_959_;
}
else
{
return v___x_954_;
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref(v_codomain_940_);
lean_dec_ref(v_e_936_);
lean_dec_ref(v_varNames_935_);
v_a_960_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_951_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_951_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_933_ = stack[0].m_obj;
lean_object* v___x_934_ = stack[1].m_obj;
lean_object* v_varNames_935_ = stack[2].m_obj;
lean_object* v_e_936_ = stack[3].m_obj;
uint8_t v___x_937_ = stack[4].m_num;
uint8_t v___x_938_ = stack[5].m_num;
lean_object* v_xs_939_ = stack[6].m_obj;
lean_object* v_codomain_940_ = stack[7].m_obj;
lean_object* v___y_941_ = stack[8].m_obj;
lean_object* v___y_942_ = stack[9].m_obj;
lean_object* v___y_943_ = stack[10].m_obj;
lean_object* v___y_944_ = stack[11].m_obj;
lean_object* v_res_968_;
v_res_968_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(v___x_933_, v___x_934_, v_varNames_935_, v_e_936_, v___x_937_, v___x_938_, v_xs_939_, v_codomain_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed(lean_object* v___x_969_, lean_object* v___x_970_, lean_object* v_varNames_971_, lean_object* v_e_972_, lean_object* v___x_973_, lean_object* v___x_974_, lean_object* v_xs_975_, lean_object* v_codomain_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v___x_799__boxed_982_; uint8_t v___x_800__boxed_983_; lean_object* v_res_984_; 
v___x_799__boxed_982_ = lean_unbox(v___x_973_);
v___x_800__boxed_983_ = lean_unbox(v___x_974_);
v_res_984_ = l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0(v___x_969_, v___x_970_, v_varNames_971_, v_e_972_, v___x_799__boxed_982_, v___x_800__boxed_983_, v_xs_975_, v_codomain_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v_xs_975_);
lean_dec(v___x_970_);
lean_dec(v___x_969_);
return v_res_984_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry(lean_object* v_varNames_990_, lean_object* v_e_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = lean_array_get_size(v_varNames_990_);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_nat_dec_eq(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = 1;
lean_inc(v_a_995_);
lean_inc_ref(v_a_994_);
lean_inc(v_a_993_);
lean_inc_ref(v_a_992_);
lean_inc_ref(v_e_991_);
v___x_1001_ = lean_infer_type(v_e_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
lean_inc_ref(v_varNames_990_);
v___x_1003_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_varNames_990_, v_a_1002_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_box(v___x_999_);
v___x_1007_ = lean_box(v___x_1000_);
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___boxed), 13, 6);
lean_closure_set(v___f_1008_, 0, v___x_1005_);
lean_closure_set(v___f_1008_, 1, v___x_998_);
lean_closure_set(v___f_1008_, 2, v_varNames_990_);
lean_closure_set(v___f_1008_, 3, v_e_991_);
lean_closure_set(v___f_1008_, 4, v___x_1006_);
lean_closure_set(v___f_1008_, 5, v___x_1007_);
v___x_1009_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1010_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_1004_, v___x_1009_, v___f_1008_, v___x_999_, v___x_999_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
return v___x_1010_;
}
else
{
lean_dec_ref(v_e_991_);
lean_dec_ref(v_varNames_990_);
return v___x_1003_;
}
}
else
{
lean_dec_ref(v_e_991_);
lean_dec_ref(v_varNames_990_);
return v___x_1001_;
}
}
else
{
lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref(v_varNames_990_);
v___x_1011_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_1012_ = 0;
v___x_1013_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_packType___closed__2, &l_Lean_Meta_ArgsPacker_Unary_packType___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_packType___closed__2);
v___x_1014_ = l_Lean_mkLambda(v___x_1011_, v___x_1012_, v___x_1013_, v_e_991_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Unary_uncurry_0interp(lean_interpreter_value* stack)
{
lean_object* v_varNames_990_ = stack[0].m_obj;
lean_object* v_e_991_ = stack[1].m_obj;
lean_object* v_a_992_ = stack[2].m_obj;
lean_object* v_a_993_ = stack[3].m_obj;
lean_object* v_a_994_ = stack[4].m_obj;
lean_object* v_a_995_ = stack[5].m_obj;
lean_object* v_res_1016_;
v_res_1016_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_varNames_990_, v_e_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
stack->m_obj
 = v_res_1016_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Unary_uncurry___boxed(lean_object* v_varNames_1017_, lean_object* v_e_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_varNames_1017_, v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1024_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__1(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___closed__0));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_dummy_1030_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_packType___closed__1));
v_dummy_1030_ = l_Lean_Expr_const___override(v___x_1029_, v___x_1028_);
return v_dummy_1030_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(lean_object* v_args_1031_, lean_object* v_type_1032_, lean_object* v_packedDomain_1033_, lean_object* v_tail_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_dummy_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_dummy_1041_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1035_);
v___x_1042_ = lean_array_push(v_args_1031_, v_x_1035_);
v___x_1043_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1032_, v_packedDomain_1033_, v_dummy_1041_, v___x_1042_, v_tail_1034_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; uint8_t v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_mk_empty_array_with_capacity(v___x_1045_);
v___x_1047_ = lean_array_push(v___x_1046_, v_x_1035_);
v___x_1048_ = 0;
v___x_1049_ = 1;
v___x_1050_ = 1;
v___x_1051_ = l_Lean_Meta_mkForallFVars(v___x_1047_, v_a_1044_, v___x_1048_, v___x_1049_, v___x_1049_, v___x_1050_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec_ref(v___x_1047_);
return v___x_1051_;
}
else
{
lean_dec_ref(v_x_1035_);
return v___x_1043_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1031_ = stack[0].m_obj;
lean_object* v_type_1032_ = stack[1].m_obj;
lean_object* v_packedDomain_1033_ = stack[2].m_obj;
lean_object* v_tail_1034_ = stack[3].m_obj;
lean_object* v_x_1035_ = stack[4].m_obj;
lean_object* v___y_1036_ = stack[5].m_obj;
lean_object* v___y_1037_ = stack[6].m_obj;
lean_object* v___y_1038_ = stack[7].m_obj;
lean_object* v___y_1039_ = stack[8].m_obj;
lean_object* v_res_1052_;
v_res_1052_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0(v_args_1031_, v_type_1032_, v_packedDomain_1033_, v_tail_1034_, v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
stack->m_obj
 = v_res_1052_;
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
uint8_t v___x_644__boxed_1076_; lean_object* v_res_1077_; 
v___x_644__boxed_1076_ = lean_unbox(v___x_1069_);
v_res_1077_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(v_arg_1064_, v_args_1065_, v_type_1066_, v_packedDomain_1067_, v_tail_1068_, v___x_644__boxed_1076_, v_x_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1077_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(lean_object* v_type_1078_, lean_object* v_packedDomain_1079_, lean_object* v_domain_1080_, lean_object* v_args_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
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
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1078_ = stack[0].m_obj;
lean_object* v_packedDomain_1079_ = stack[1].m_obj;
lean_object* v_domain_1080_ = stack[2].m_obj;
lean_object* v_args_1081_ = stack[3].m_obj;
lean_object* v_a_1082_ = stack[4].m_obj;
lean_object* v_a_1083_ = stack[5].m_obj;
lean_object* v_a_1084_ = stack[6].m_obj;
lean_object* v_a_1085_ = stack[7].m_obj;
lean_object* v_a_1086_ = stack[8].m_obj;
lean_object* v_res_1119_;
v_res_1119_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1078_, v_packedDomain_1079_, v_domain_1080_, v_args_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
stack->m_obj
 = v_res_1119_;
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(lean_object* v_arg_1120_, lean_object* v_args_1121_, lean_object* v_type_1122_, lean_object* v_packedDomain_1123_, lean_object* v_tail_1124_, uint8_t v___x_1125_, lean_object* v_x_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_mk_empty_array_with_capacity(v___x_1132_);
lean_inc_ref(v_x_1126_);
v___x_1134_ = lean_array_push(v___x_1133_, v_x_1126_);
lean_inc_ref(v___x_1134_);
v___x_1135_ = l_Lean_Expr_beta(v_arg_1120_, v___x_1134_);
v___x_1136_ = lean_array_push(v_args_1121_, v_x_1126_);
v___x_1137_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1122_, v_packedDomain_1123_, v___x_1135_, v___x_1136_, v_tail_1124_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; uint8_t v___x_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = 0;
v___x_1140_ = 1;
v___x_1141_ = l_Lean_Meta_mkForallFVars(v___x_1134_, v_a_1138_, v___x_1139_, v___x_1125_, v___x_1125_, v___x_1140_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec_ref(v___x_1134_);
return v___x_1141_;
}
else
{
lean_dec_ref(v___x_1134_);
return v___x_1137_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_1120_ = stack[0].m_obj;
lean_object* v_args_1121_ = stack[1].m_obj;
lean_object* v_type_1122_ = stack[2].m_obj;
lean_object* v_packedDomain_1123_ = stack[3].m_obj;
lean_object* v_tail_1124_ = stack[4].m_obj;
uint8_t v___x_1125_ = stack[5].m_num;
lean_object* v_x_1126_ = stack[6].m_obj;
lean_object* v___y_1127_ = stack[7].m_obj;
lean_object* v___y_1128_ = stack[8].m_obj;
lean_object* v___y_1129_ = stack[9].m_obj;
lean_object* v___y_1130_ = stack[10].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(v_arg_1120_, v_args_1121_, v_type_1122_, v_packedDomain_1123_, v_tail_1124_, v___x_1125_, v_x_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___boxed(lean_object* v_type_1143_, lean_object* v_packedDomain_1144_, lean_object* v_domain_1145_, lean_object* v_args_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1143_, v_packedDomain_1144_, v_domain_1145_, v_args_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1153_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__0));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(lean_object* v_varNames_1157_, lean_object* v_type_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v___x_1173_; 
v___x_1173_ = l_Lean_Expr_isForall(v_type_1158_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_varNames_1157_);
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_1175_ = l_Lean_MessageData_ofExpr(v_type_1158_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1176_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
v___y_1165_ = v_a_1159_;
v___y_1166_ = v_a_1160_;
v___y_1167_ = v_a_1161_;
v___y_1168_ = v_a_1162_;
goto v___jp_1164_;
}
v___jp_1164_:
{
lean_object* v_packedDomain_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_packedDomain_1169_ = l_Lean_Expr_bindingDomain_x21(v_type_1158_);
v___x_1170_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1171_ = lean_array_to_list(v_varNames_1157_);
lean_inc_ref(v_packedDomain_1169_);
v___x_1172_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go(v_type_1158_, v_packedDomain_1169_, v_packedDomain_1169_, v___x_1170_, v___x_1171_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v___x_1172_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_0interp(lean_interpreter_value* stack)
{
lean_object* v_varNames_1157_ = stack[0].m_obj;
lean_object* v_type_1158_ = stack[1].m_obj;
lean_object* v_a_1159_ = stack[2].m_obj;
lean_object* v_a_1160_ = stack[3].m_obj;
lean_object* v_a_1161_ = stack[4].m_obj;
lean_object* v_a_1162_ = stack[5].m_obj;
lean_object* v_res_1186_;
v_res_1186_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_varNames_1157_, v_type_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
stack->m_obj
 = v_res_1186_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___boxed(lean_object* v_varNames_1187_, lean_object* v_type_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_varNames_1187_, v_type_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
return v_res_1194_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__0));
v___x_1197_ = l_Lean_stringToMessageData(v___x_1196_);
return v___x_1197_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(lean_object* v_args_1198_, lean_object* v_e_1199_, lean_object* v_packedDomain_1200_, lean_object* v_tail_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_dummy_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_dummy_1208_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__0___closed__0);
lean_inc_ref(v_x_1202_);
v___x_1209_ = lean_array_push(v_args_1198_, v_x_1202_);
v___x_1210_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1199_, v_packedDomain_1200_, v_dummy_1208_, v___x_1209_, v_tail_1201_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; uint8_t v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_mk_empty_array_with_capacity(v___x_1212_);
v___x_1214_ = lean_array_push(v___x_1213_, v_x_1202_);
v___x_1215_ = 0;
v___x_1216_ = 1;
v___x_1217_ = 1;
v___x_1218_ = l_Lean_Meta_mkLambdaFVars(v___x_1214_, v_a_1211_, v___x_1215_, v___x_1216_, v___x_1215_, v___x_1216_, v___x_1217_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec_ref(v___x_1214_);
return v___x_1218_;
}
else
{
lean_dec_ref(v_x_1202_);
return v___x_1210_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1198_ = stack[0].m_obj;
lean_object* v_e_1199_ = stack[1].m_obj;
lean_object* v_packedDomain_1200_ = stack[2].m_obj;
lean_object* v_tail_1201_ = stack[3].m_obj;
lean_object* v_x_1202_ = stack[4].m_obj;
lean_object* v___y_1203_ = stack[5].m_obj;
lean_object* v___y_1204_ = stack[6].m_obj;
lean_object* v___y_1205_ = stack[7].m_obj;
lean_object* v___y_1206_ = stack[8].m_obj;
lean_object* v_res_1219_;
v_res_1219_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(v_args_1198_, v_e_1199_, v_packedDomain_1200_, v_tail_1201_, v_x_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
stack->m_obj
 = v_res_1219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed(lean_object* v_args_1220_, lean_object* v_e_1221_, lean_object* v_packedDomain_1222_, lean_object* v_tail_1223_, lean_object* v_x_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0(v_args_1220_, v_e_1221_, v_packedDomain_1222_, v_tail_1223_, v_x_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed(lean_object* v_arg_1231_, lean_object* v_args_1232_, lean_object* v_e_1233_, lean_object* v_packedDomain_1234_, lean_object* v_tail_1235_, lean_object* v___x_1236_, lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v___x_762__boxed_1243_; lean_object* v_res_1244_; 
v___x_762__boxed_1243_ = lean_unbox(v___x_1236_);
v_res_1244_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(v_arg_1231_, v_args_1232_, v_e_1233_, v_packedDomain_1234_, v_tail_1235_, v___x_762__boxed_1243_, v_x_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1244_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(lean_object* v_e_1245_, lean_object* v_packedDomain_1246_, lean_object* v_domain_1247_, lean_object* v_args_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; 
if (lean_obj_tag(v_a_1249_) == 0)
{
lean_object* v_packedArg_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v_domain_1247_);
v_packedArg_1264_ = l_Lean_Meta_ArgsPacker_Unary_pack(v_packedDomain_1246_, v_args_1248_);
lean_dec_ref(v_args_1248_);
lean_dec_ref(v_packedDomain_1246_);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_mk_empty_array_with_capacity(v___x_1265_);
v___x_1267_ = lean_array_push(v___x_1266_, v_packedArg_1264_);
v___x_1268_ = l_Lean_Expr_beta(v_e_1245_, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
else
{
lean_object* v_tail_1270_; 
v_tail_1270_ = lean_ctor_get(v_a_1249_, 1);
lean_inc(v_tail_1270_);
if (lean_obj_tag(v_tail_1270_) == 0)
{
lean_object* v_head_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; 
v_head_1271_ = lean_ctor_get(v_a_1249_, 0);
lean_inc(v_head_1271_);
lean_dec_ref_known(v_a_1249_, 2);
v___f_1272_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1272_, 0, v_args_1248_);
lean_closure_set(v___f_1272_, 1, v_e_1245_);
lean_closure_set(v___f_1272_, 2, v_packedDomain_1246_);
lean_closure_set(v___f_1272_, 3, v_tail_1270_);
v___x_1273_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1271_, v_domain_1247_, v___f_1272_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
return v___x_1273_;
}
else
{
lean_object* v_head_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_head_1274_ = lean_ctor_get(v_a_1249_, 0);
lean_inc(v_head_1274_);
lean_dec_ref_known(v_a_1249_, 2);
lean_inc_ref(v_domain_1247_);
v___x_1275_ = l_Lean_Expr_cleanupAnnotations(v_domain_1247_);
v___x_1276_ = l_Lean_Expr_isApp(v___x_1275_);
if (v___x_1276_ == 0)
{
lean_dec_ref(v___x_1275_);
lean_dec(v_head_1274_);
lean_dec(v_tail_1270_);
lean_dec_ref(v_args_1248_);
lean_dec_ref(v_packedDomain_1246_);
lean_dec_ref(v_e_1245_);
v___y_1256_ = v_a_1250_;
v___y_1257_ = v_a_1251_;
v___y_1258_ = v_a_1252_;
v___y_1259_ = v_a_1253_;
goto v___jp_1255_;
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
lean_dec(v_head_1274_);
lean_dec(v_tail_1270_);
lean_dec_ref(v_args_1248_);
lean_dec_ref(v_packedDomain_1246_);
lean_dec_ref(v_e_1245_);
v___y_1256_ = v_a_1250_;
v___y_1257_ = v_a_1251_;
v___y_1258_ = v_a_1252_;
v___y_1259_ = v_a_1253_;
goto v___jp_1255_;
}
else
{
lean_object* v_arg_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_arg_1280_ = lean_ctor_get(v___x_1278_, 1);
lean_inc_ref(v_arg_1280_);
v___x_1281_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1278_);
v___x_1282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1283_ = l_Lean_Expr_isConstOf(v___x_1281_, v___x_1282_);
lean_dec_ref(v___x_1281_);
if (v___x_1283_ == 0)
{
lean_dec_ref(v_arg_1280_);
lean_dec_ref(v_arg_1277_);
lean_dec(v_head_1274_);
lean_dec(v_tail_1270_);
lean_dec_ref(v_args_1248_);
lean_dec_ref(v_packedDomain_1246_);
lean_dec_ref(v_e_1245_);
v___y_1256_ = v_a_1250_;
v___y_1257_ = v_a_1251_;
v___y_1258_ = v_a_1252_;
v___y_1259_ = v_a_1253_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; 
lean_dec_ref(v_domain_1247_);
v___x_1284_ = lean_box(v___x_1283_);
v___f_1285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1285_, 0, v_arg_1277_);
lean_closure_set(v___f_1285_, 1, v_args_1248_);
lean_closure_set(v___f_1285_, 2, v_e_1245_);
lean_closure_set(v___f_1285_, 3, v_packedDomain_1246_);
lean_closure_set(v___f_1285_, 4, v_tail_1270_);
lean_closure_set(v___f_1285_, 5, v___x_1284_);
v___x_1286_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1274_, v_arg_1280_, v___f_1285_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
return v___x_1286_;
}
}
}
}
}
v___jp_1255_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___closed__1);
v___x_1261_ = l_Lean_MessageData_ofExpr(v_domain_1247_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1262_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
return v___x_1263_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1245_ = stack[0].m_obj;
lean_object* v_packedDomain_1246_ = stack[1].m_obj;
lean_object* v_domain_1247_ = stack[2].m_obj;
lean_object* v_args_1248_ = stack[3].m_obj;
lean_object* v_a_1249_ = stack[4].m_obj;
lean_object* v_a_1250_ = stack[5].m_obj;
lean_object* v_a_1251_ = stack[6].m_obj;
lean_object* v_a_1252_ = stack[7].m_obj;
lean_object* v_a_1253_ = stack[8].m_obj;
lean_object* v_res_1287_;
v_res_1287_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1245_, v_packedDomain_1246_, v_domain_1247_, v_args_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
stack->m_obj
 = v_res_1287_;
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(lean_object* v_arg_1288_, lean_object* v_args_1289_, lean_object* v_e_1290_, lean_object* v_packedDomain_1291_, lean_object* v_tail_1292_, uint8_t v___x_1293_, lean_object* v_x_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_mk_empty_array_with_capacity(v___x_1300_);
lean_inc_ref(v_x_1294_);
v___x_1302_ = lean_array_push(v___x_1301_, v_x_1294_);
lean_inc_ref(v___x_1302_);
v___x_1303_ = l_Lean_Expr_beta(v_arg_1288_, v___x_1302_);
v___x_1304_ = lean_array_push(v_args_1289_, v_x_1294_);
v___x_1305_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1290_, v_packedDomain_1291_, v___x_1303_, v___x_1304_, v_tail_1292_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; uint8_t v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = 0;
v___x_1308_ = 1;
v___x_1309_ = l_Lean_Meta_mkLambdaFVars(v___x_1302_, v_a_1306_, v___x_1307_, v___x_1293_, v___x_1307_, v___x_1293_, v___x_1308_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec_ref(v___x_1302_);
return v___x_1309_;
}
else
{
lean_dec_ref(v___x_1302_);
return v___x_1305_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_1288_ = stack[0].m_obj;
lean_object* v_args_1289_ = stack[1].m_obj;
lean_object* v_e_1290_ = stack[2].m_obj;
lean_object* v_packedDomain_1291_ = stack[3].m_obj;
lean_object* v_tail_1292_ = stack[4].m_obj;
uint8_t v___x_1293_ = stack[5].m_num;
lean_object* v_x_1294_ = stack[6].m_obj;
lean_object* v___y_1295_ = stack[7].m_obj;
lean_object* v___y_1296_ = stack[8].m_obj;
lean_object* v___y_1297_ = stack[9].m_obj;
lean_object* v___y_1298_ = stack[10].m_obj;
lean_object* v_res_1310_;
v_res_1310_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(v_arg_1288_, v_args_1289_, v_e_1290_, v_packedDomain_1291_, v_tail_1292_, v___x_1293_, v_x_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
stack->m_obj
 = v_res_1310_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___boxed(lean_object* v_e_1311_, lean_object* v_packedDomain_1312_, lean_object* v_domain_1313_, lean_object* v_args_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1311_, v_packedDomain_1312_, v_domain_1313_, v_args_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1321_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__0));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Unary_pack___closed__2, &l_Lean_Meta_ArgsPacker_Unary_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_Unary_pack___closed__2);
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = lean_mk_empty_array_with_capacity(v___x_1326_);
v___x_1328_ = lean_array_push(v___x_1327_, v___x_1325_);
return v___x_1328_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(lean_object* v_varNames_1329_, lean_object* v_e_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1336_ = lean_array_get_size(v_varNames_1329_);
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = lean_nat_dec_eq(v___x_1336_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_inc(v_a_1334_);
lean_inc_ref(v_a_1333_);
lean_inc(v_a_1332_);
lean_inc_ref(v_a_1331_);
lean_inc_ref(v_e_1330_);
v___x_1339_ = lean_infer_type(v_e_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
v___x_1341_ = l_Lean_Meta_whnfForall(v_a_1340_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v___x_1352_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1352_ = l_Lean_Expr_isForall(v_a_1342_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_e_1330_);
lean_dec_ref(v_varNames_1329_);
v___x_1353_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__1);
v___x_1354_ = l_Lean_MessageData_ofExpr(v_a_1342_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1355_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
v___y_1344_ = v_a_1331_;
v___y_1345_ = v_a_1332_;
v___y_1346_ = v_a_1333_;
v___y_1347_ = v_a_1334_;
goto v___jp_1343_;
}
v___jp_1343_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1348_ = l_Lean_Expr_bindingDomain_x21(v_a_1342_);
lean_dec(v_a_1342_);
v___x_1349_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_1350_ = lean_array_to_list(v_varNames_1329_);
lean_inc_ref(v___x_1348_);
v___x_1351_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go(v_e_1330_, v___x_1348_, v___x_1348_, v___x_1349_, v___x_1350_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1351_;
}
}
else
{
lean_dec_ref(v_e_1330_);
lean_dec_ref(v_varNames_1329_);
return v___x_1341_;
}
}
else
{
lean_dec_ref(v_e_1330_);
lean_dec_ref(v_varNames_1329_);
return v___x_1339_;
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec_ref(v_varNames_1329_);
v___x_1365_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___closed__2);
v___x_1366_ = l_Lean_Expr_beta(v_e_1330_, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_0interp(lean_interpreter_value* stack)
{
lean_object* v_varNames_1329_ = stack[0].m_obj;
lean_object* v_e_1330_ = stack[1].m_obj;
lean_object* v_a_1331_ = stack[2].m_obj;
lean_object* v_a_1332_ = stack[3].m_obj;
lean_object* v_a_1333_ = stack[4].m_obj;
lean_object* v_a_1334_ = stack[5].m_obj;
lean_object* v_res_1368_;
v_res_1368_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v_varNames_1329_, v_e_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
stack->m_obj
 = v_res_1368_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry___boxed(lean_object* v_varNames_1369_, lean_object* v_e_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v_varNames_1369_, v_e_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
return v_res_1376_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(lean_object* v_as_1380_, size_t v_sz_1381_, size_t v_i_1382_, lean_object* v_b_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_usize_dec_lt(v_i_1382_, v_sz_1381_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_b_1383_);
return v___x_1390_;
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_a_1391_ = lean_array_uget_borrowed(v_as_1380_, v_i_1382_);
v___x_1392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1393_ = lean_unsigned_to_nat(2u);
v___x_1394_ = lean_mk_empty_array_with_capacity(v___x_1393_);
lean_inc(v_a_1391_);
v___x_1395_ = lean_array_push(v___x_1394_, v_a_1391_);
v___x_1396_ = lean_array_push(v___x_1395_, v_b_1383_);
v___x_1397_ = l_Lean_Meta_mkAppM(v___x_1392_, v___x_1396_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; size_t v___x_1399_; size_t v___x_1400_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = ((size_t)1ULL);
v___x_1400_ = lean_usize_add(v_i_1382_, v___x_1399_);
v_i_1382_ = v___x_1400_;
v_b_1383_ = v_a_1398_;
goto _start;
}
else
{
return v___x_1397_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1380_ = stack[0].m_obj;
size_t v_sz_1381_ = stack[1].m_num;
size_t v_i_1382_ = stack[2].m_num;
lean_object* v_b_1383_ = stack[3].m_obj;
lean_object* v___y_1384_ = stack[4].m_obj;
lean_object* v___y_1385_ = stack[5].m_obj;
lean_object* v___y_1386_ = stack[6].m_obj;
lean_object* v___y_1387_ = stack[7].m_obj;
lean_object* v_res_1402_;
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v_as_1380_, v_sz_1381_, v_i_1382_, v_b_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
stack->m_obj
 = v_res_1402_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___boxed(lean_object* v_as_1403_, lean_object* v_sz_1404_, lean_object* v_i_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
size_t v_sz_boxed_1412_; size_t v_i_boxed_1413_; lean_object* v_res_1414_; 
v_sz_boxed_1412_ = lean_unbox_usize(v_sz_1404_);
lean_dec(v_sz_1404_);
v_i_boxed_1413_ = lean_unbox_usize(v_i_1405_);
lean_dec(v_i_1405_);
v_res_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v_as_1403_, v_sz_boxed_1412_, v_i_boxed_1413_, v_b_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec_ref(v_as_1403_);
return v_res_1414_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object* v_ds_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_r_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; size_t v_sz_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
v___x_1421_ = l_Lean_instInhabitedExpr;
v___x_1422_ = lean_array_get_size(v_ds_1415_);
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_nat_sub(v___x_1422_, v___x_1423_);
v_r_1425_ = lean_array_get(v___x_1421_, v_ds_1415_, v___x_1424_);
lean_dec(v___x_1424_);
v___x_1426_ = lean_array_pop(v_ds_1415_);
v___x_1427_ = l_Array_reverse___redArg(v___x_1426_);
v_sz_1428_ = lean_array_size(v___x_1427_);
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0(v___x_1427_, v_sz_1428_, v___x_1429_, v_r_1425_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec_ref(v___x_1427_);
return v___x_1430_;
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_packType_0interp(lean_interpreter_value* stack)
{
lean_object* v_ds_1415_ = stack[0].m_obj;
lean_object* v_a_1416_ = stack[1].m_obj;
lean_object* v_a_1417_ = stack[2].m_obj;
lean_object* v_a_1418_ = stack[3].m_obj;
lean_object* v_a_1419_ = stack[4].m_obj;
lean_object* v_res_1431_;
v_res_1431_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v_ds_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
stack->m_obj
 = v_res_1431_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object* v_ds_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v_ds_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
return v_res_1438_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0));
v___x_1441_ = l_Lean_stringToMessageData(v___x_1440_);
return v___x_1441_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object* v_n_1442_, lean_object* v_type_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v_zero_1458_; uint8_t v_isZero_1459_; 
v_zero_1458_ = lean_unsigned_to_nat(0u);
v_isZero_1459_ = lean_nat_dec_eq(v_n_1442_, v_zero_1458_);
if (v_isZero_1459_ == 1)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec_ref(v_type_1443_);
v___x_1460_ = lean_box(0);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
else
{
lean_object* v_one_1462_; lean_object* v_n_1463_; uint8_t v___x_1464_; 
v_one_1462_ = lean_unsigned_to_nat(1u);
v_n_1463_ = lean_nat_sub(v_n_1442_, v_one_1462_);
v___x_1464_ = lean_nat_dec_eq(v_n_1463_, v_zero_1458_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
lean_inc_ref(v_type_1443_);
v___x_1465_ = l_Lean_Expr_cleanupAnnotations(v_type_1443_);
v___x_1466_ = l_Lean_Expr_isApp(v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec_ref(v___x_1465_);
lean_dec(v_n_1463_);
v___y_1450_ = v_a_1444_;
v___y_1451_ = v_a_1445_;
v___y_1452_ = v_a_1446_;
v___y_1453_ = v_a_1447_;
goto v___jp_1449_;
}
else
{
lean_object* v_arg_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_arg_1467_ = lean_ctor_get(v___x_1465_, 1);
lean_inc_ref(v_arg_1467_);
v___x_1468_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1465_);
v___x_1469_ = l_Lean_Expr_isApp(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_dec_ref(v___x_1468_);
lean_dec_ref(v_arg_1467_);
lean_dec(v_n_1463_);
v___y_1450_ = v_a_1444_;
v___y_1451_ = v_a_1445_;
v___y_1452_ = v_a_1446_;
v___y_1453_ = v_a_1447_;
goto v___jp_1449_;
}
else
{
lean_object* v_arg_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_arg_1470_ = lean_ctor_get(v___x_1468_, 1);
lean_inc_ref(v_arg_1470_);
v___x_1471_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1468_);
v___x_1472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1473_ = l_Lean_Expr_isConstOf(v___x_1471_, v___x_1472_);
lean_dec_ref(v___x_1471_);
if (v___x_1473_ == 0)
{
lean_dec_ref(v_arg_1470_);
lean_dec_ref(v_arg_1467_);
lean_dec(v_n_1463_);
v___y_1450_ = v_a_1444_;
v___y_1451_ = v_a_1445_;
v___y_1452_ = v_a_1446_;
v___y_1453_ = v_a_1447_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1474_; 
lean_dec_ref(v_type_1443_);
v___x_1474_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1463_, v_arg_1467_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_n_1463_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1483_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1483_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1483_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_arg_1470_);
lean_ctor_set(v___x_1479_, 1, v_a_1475_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1479_);
v___x_1481_ = v___x_1477_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
else
{
lean_dec_ref(v_arg_1470_);
return v___x_1474_;
}
}
}
}
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec(v_n_1463_);
v___x_1484_ = lean_box(0);
v___x_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_type_1443_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
v___jp_1449_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1);
v___x_1455_ = l_Lean_MessageData_ofExpr(v_type_1443_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1456_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1457_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1442_ = stack[0].m_obj;
lean_object* v_type_1443_ = stack[1].m_obj;
lean_object* v_a_1444_ = stack[2].m_obj;
lean_object* v_a_1445_ = stack[3].m_obj;
lean_object* v_a_1446_ = stack[4].m_obj;
lean_object* v_a_1447_ = stack[5].m_obj;
lean_object* v_res_1487_;
v_res_1487_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1442_, v_type_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
stack->m_obj
 = v_res_1487_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object* v_n_1488_, lean_object* v_type_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1488_, v_type_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_n_1488_);
return v_res_1495_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0(void){
_start:
{
lean_object* v___x_1496_; lean_object* v_dummy_1497_; 
v___x_1496_ = lean_box(0);
v_dummy_1497_ = l_Lean_Expr_sort___override(v___x_1496_);
return v_dummy_1497_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1500_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__1));
v___x_1501_ = lean_unsigned_to_nat(8u);
v___x_1502_ = lean_unsigned_to_nat(276u);
v___x_1503_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__0));
v___x_1504_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1505_ = l_mkPanicMessageWithDecl(v___x_1504_, v___x_1503_, v___x_1502_, v___x_1501_, v___x_1500_);
return v___x_1505_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(lean_object* v_i_1514_, lean_object* v_fidx_1515_, lean_object* v_numFuncs_1516_, lean_object* v_arg_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_x_1518_) == 5)
{
lean_object* v_fn_1527_; lean_object* v_arg_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_fn_1527_ = lean_ctor_get(v_x_1518_, 0);
lean_inc_ref(v_fn_1527_);
v_arg_1528_ = lean_ctor_get(v_x_1518_, 1);
lean_inc_ref(v_arg_1528_);
lean_dec_ref_known(v_x_1518_, 2);
v___x_1529_ = lean_array_set(v_x_1519_, v_x_1520_, v_arg_1528_);
v___x_1530_ = lean_nat_sub(v_x_1520_, v___x_1526_);
lean_dec(v_x_1520_);
v_x_1518_ = v_fn_1527_;
v_x_1519_ = v___x_1529_;
v_x_1520_ = v___x_1530_;
goto _start;
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
lean_dec(v_x_1520_);
v___x_1532_ = lean_array_get_size(v_x_1519_);
v___x_1533_ = lean_unsigned_to_nat(2u);
v___x_1534_ = lean_nat_dec_eq(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec_ref(v_x_1519_);
lean_dec_ref(v_x_1518_);
lean_dec_ref(v_arg_1517_);
v___x_1535_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__2);
v___x_1536_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1535_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v___x_1536_;
}
else
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = l_Lean_instInhabitedExpr;
v___x_1538_ = lean_nat_dec_eq(v_i_1514_, v_fidx_1515_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_nat_add(v_i_1514_, v___x_1526_);
v___x_1540_ = lean_array_get(v___x_1537_, v_x_1519_, v___x_1526_);
lean_inc(v___x_1540_);
v___x_1541_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1516_, v_fidx_1515_, v_arg_1517_, v___x_1539_, v___x_1540_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___x_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1555_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1555_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1555_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1546_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1547_ = l_Lean_Expr_constLevels_x21(v_x_1518_);
lean_dec_ref(v_x_1518_);
v___x_1548_ = l_Lean_mkConst(v___x_1546_, v___x_1547_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = lean_array_get(v___x_1537_, v_x_1519_, v___x_1549_);
lean_dec_ref(v_x_1519_);
v___x_1551_ = l_Lean_mkApp3(v___x_1548_, v___x_1550_, v___x_1540_, v_a_1542_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1551_);
v___x_1553_ = v___x_1544_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
else
{
lean_dec(v___x_1540_);
lean_dec_ref(v_x_1519_);
lean_dec_ref(v_x_1518_);
return v___x_1541_;
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1556_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1557_ = l_Lean_Expr_constLevels_x21(v_x_1518_);
lean_dec_ref(v_x_1518_);
v___x_1558_ = l_Lean_mkConst(v___x_1556_, v___x_1557_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = lean_array_get(v___x_1537_, v_x_1519_, v___x_1559_);
v___x_1561_ = lean_array_get(v___x_1537_, v_x_1519_, v___x_1526_);
lean_dec_ref(v_x_1519_);
v___x_1562_ = l_Lean_mkApp3(v___x_1558_, v___x_1560_, v___x_1561_, v_arg_1517_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1514_ = stack[0].m_obj;
lean_object* v_fidx_1515_ = stack[1].m_obj;
lean_object* v_numFuncs_1516_ = stack[2].m_obj;
lean_object* v_arg_1517_ = stack[3].m_obj;
lean_object* v_x_1518_ = stack[4].m_obj;
lean_object* v_x_1519_ = stack[5].m_obj;
lean_object* v_x_1520_ = stack[6].m_obj;
lean_object* v___y_1521_ = stack[7].m_obj;
lean_object* v___y_1522_ = stack[8].m_obj;
lean_object* v___y_1523_ = stack[9].m_obj;
lean_object* v___y_1524_ = stack[10].m_obj;
lean_object* v_res_1564_;
v_res_1564_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1514_, v_fidx_1515_, v_numFuncs_1516_, v_arg_1517_, v_x_1518_, v_x_1519_, v_x_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
stack->m_obj
 = v_res_1564_;
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(lean_object* v_numFuncs_1565_, lean_object* v_fidx_1566_, lean_object* v_arg_1567_, lean_object* v_i_1568_, lean_object* v_type_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1575_ = lean_unsigned_to_nat(1u);
v___x_1576_ = lean_nat_sub(v_numFuncs_1565_, v___x_1575_);
v___x_1577_ = lean_nat_dec_le(v___x_1576_, v_i_1568_);
lean_dec(v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Meta_whnfD(v_type_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v_dummy_1580_; lean_object* v_nargs_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v_dummy_1580_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
v_nargs_1581_ = l_Lean_Expr_getAppNumArgs(v_a_1579_);
lean_inc(v_nargs_1581_);
v___x_1582_ = lean_mk_array(v_nargs_1581_, v_dummy_1580_);
v___x_1583_ = lean_nat_sub(v_nargs_1581_, v___x_1575_);
lean_dec(v_nargs_1581_);
v___x_1584_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1568_, v_fidx_1566_, v_numFuncs_1565_, v_arg_1567_, v_a_1579_, v___x_1582_, v___x_1583_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
return v___x_1584_;
}
else
{
lean_dec_ref(v_arg_1567_);
return v___x_1578_;
}
}
else
{
lean_object* v___x_1585_; 
lean_dec_ref(v_type_1569_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_arg_1567_);
return v___x_1585_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_numFuncs_1565_ = stack[0].m_obj;
lean_object* v_fidx_1566_ = stack[1].m_obj;
lean_object* v_arg_1567_ = stack[2].m_obj;
lean_object* v_i_1568_ = stack[3].m_obj;
lean_object* v_type_1569_ = stack[4].m_obj;
lean_object* v_a_1570_ = stack[5].m_obj;
lean_object* v_a_1571_ = stack[6].m_obj;
lean_object* v_a_1572_ = stack[7].m_obj;
lean_object* v_a_1573_ = stack[8].m_obj;
lean_object* v_res_1586_;
v_res_1586_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1565_, v_fidx_1566_, v_arg_1567_, v_i_1568_, v_type_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
stack->m_obj
 = v_res_1586_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___boxed(lean_object* v_numFuncs_1587_, lean_object* v_fidx_1588_, lean_object* v_arg_1589_, lean_object* v_i_1590_, lean_object* v_type_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1587_, v_fidx_1588_, v_arg_1589_, v_i_1590_, v_type_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_i_1590_);
lean_dec(v_fidx_1588_);
lean_dec(v_numFuncs_1587_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___boxed(lean_object* v_i_1598_, lean_object* v_fidx_1599_, lean_object* v_numFuncs_1600_, lean_object* v_arg_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0(v_i_1598_, v_fidx_1599_, v_numFuncs_1600_, v_arg_1601_, v_x_1602_, v_x_1603_, v_x_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v_numFuncs_1600_);
lean_dec(v_fidx_1599_);
lean_dec(v_i_1598_);
return v_res_1610_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object* v_numFuncs_1611_, lean_object* v_domain_1612_, lean_object* v_fidx_1613_, lean_object* v_arg_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go(v_numFuncs_1611_, v_fidx_1613_, v_arg_1614_, v___x_1620_, v_domain_1612_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
return v___x_1621_;
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_pack_0interp(lean_interpreter_value* stack)
{
lean_object* v_numFuncs_1611_ = stack[0].m_obj;
lean_object* v_domain_1612_ = stack[1].m_obj;
lean_object* v_fidx_1613_ = stack[2].m_obj;
lean_object* v_arg_1614_ = stack[3].m_obj;
lean_object* v_a_1615_ = stack[4].m_obj;
lean_object* v_a_1616_ = stack[5].m_obj;
lean_object* v_a_1617_ = stack[6].m_obj;
lean_object* v_a_1618_ = stack[7].m_obj;
lean_object* v_res_1622_;
v_res_1622_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v_numFuncs_1611_, v_domain_1612_, v_fidx_1613_, v_arg_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
stack->m_obj
 = v_res_1622_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object* v_numFuncs_1623_, lean_object* v_domain_1624_, lean_object* v_fidx_1625_, lean_object* v_arg_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v_numFuncs_1623_, v_domain_1624_, v_fidx_1625_, v_arg_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_fidx_1625_);
lean_dec(v_numFuncs_1623_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(lean_object* v_numFuncs_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_fst_1635_; lean_object* v_snd_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1671_; 
v_fst_1635_ = lean_ctor_get(v_a_1634_, 0);
v_snd_1636_ = lean_ctor_get(v_a_1634_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_a_1634_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1638_ = v_a_1634_;
v_isShared_1639_ = v_isSharedCheck_1671_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_snd_1636_);
lean_inc(v_fst_1635_);
lean_dec(v_a_1634_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1671_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1640_ = lean_unsigned_to_nat(1u);
v___x_1641_ = lean_nat_add(v_fst_1635_, v___x_1640_);
v___x_1642_ = lean_nat_dec_lt(v___x_1641_, v_numFuncs_1633_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1644_; 
lean_dec(v___x_1641_);
if (v_isShared_1639_ == 0)
{
v___x_1644_ = v___x_1638_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_fst_1635_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_snd_1636_);
v___x_1644_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__4));
v___x_1648_ = lean_unsigned_to_nat(3u);
v___x_1649_ = l_Lean_Expr_isAppOfArity(v_snd_1636_, v___x_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
lean_dec(v___x_1641_);
v___x_1650_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__6));
v___x_1651_ = l_Lean_Expr_isAppOfArity(v_snd_1636_, v___x_1650_, v___x_1648_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_del_object(v___x_1638_);
lean_dec(v_snd_1636_);
lean_dec(v_fst_1635_);
v___x_1652_ = lean_box(0);
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1653_ = lean_unsigned_to_nat(2u);
v___x_1654_ = l_Lean_Expr_getAppNumArgs(v_snd_1636_);
v___x_1655_ = lean_nat_sub(v___x_1654_, v___x_1653_);
lean_dec(v___x_1654_);
v___x_1656_ = lean_nat_sub(v___x_1655_, v___x_1640_);
lean_dec(v___x_1655_);
v___x_1657_ = l_Lean_Expr_getRevArg_x21(v_snd_1636_, v___x_1656_);
lean_dec(v_snd_1636_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 1, v___x_1657_);
v___x_1659_ = v___x_1638_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_fst_1635_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
lean_dec(v_fst_1635_);
v___x_1662_ = lean_unsigned_to_nat(2u);
v___x_1663_ = l_Lean_Expr_getAppNumArgs(v_snd_1636_);
v___x_1664_ = lean_nat_sub(v___x_1663_, v___x_1662_);
lean_dec(v___x_1663_);
v___x_1665_ = lean_nat_sub(v___x_1664_, v___x_1640_);
lean_dec(v___x_1664_);
v___x_1666_ = l_Lean_Expr_getRevArg_x21(v_snd_1636_, v___x_1665_);
lean_dec(v_snd_1636_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 1, v___x_1666_);
lean_ctor_set(v___x_1638_, 0, v___x_1641_);
v___x_1668_ = v___x_1638_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
v_a_1634_ = v___x_1668_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg___boxed(lean_object* v_numFuncs_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1672_, v_a_1673_);
lean_dec(v_numFuncs_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object* v_numFuncs_1675_, lean_object* v_expr_1676_){
_start:
{
lean_object* v_funidx_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_funidx_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v_funidx_1677_);
lean_ctor_set(v___x_1678_, 1, v_expr_1676_);
v___x_1679_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1675_, v___x_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
return v___x_1679_;
}
else
{
lean_object* v_val_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1696_; 
v_val_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1696_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_val_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1696_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_fst_1684_; lean_object* v_snd_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1695_; 
v_fst_1684_ = lean_ctor_get(v_val_1680_, 0);
v_snd_1685_ = lean_ctor_get(v_val_1680_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_val_1680_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1687_ = v_val_1680_;
v_isShared_1688_ = v_isSharedCheck_1695_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_snd_1685_);
lean_inc(v_fst_1684_);
lean_dec(v_val_1680_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1695_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_fst_1684_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_snd_1685_);
v___x_1690_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1692_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1690_);
v___x_1692_ = v___x_1682_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack___boxed(lean_object* v_numFuncs_1697_, lean_object* v_expr_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v_numFuncs_1697_, v_expr_1698_);
lean_dec(v_numFuncs_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(lean_object* v_numFuncs_1700_, lean_object* v_inst_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___redArg(v_numFuncs_1700_, v_a_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0___boxed(lean_object* v_numFuncs_1704_, lean_object* v_inst_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_ArgsPacker_Mutual_unpack_spec__0(v_numFuncs_1704_, v_inst_1705_, v_a_1706_);
lean_dec(v_numFuncs_1704_);
return v_res_1707_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object* v___x_1708_, lean_object* v___x_1709_, lean_object* v_types_1710_, lean_object* v_i_1711_, uint8_t v___x_1712_, uint8_t v___x_1713_, uint8_t v___x_1714_, lean_object* v_x_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_inc_ref(v_x_1715_);
v___x_1721_ = lean_array_push(v___x_1708_, v_x_1715_);
v___x_1722_ = lean_array_get_borrowed(v___x_1709_, v_types_1710_, v_i_1711_);
v___x_1723_ = l_Lean_Expr_bindingBody_x21(v___x_1722_);
v___x_1724_ = lean_expr_instantiate1(v___x_1723_, v_x_1715_);
lean_dec_ref(v_x_1715_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = l_Lean_Meta_mkLambdaFVars(v___x_1721_, v___x_1724_, v___x_1712_, v___x_1713_, v___x_1712_, v___x_1713_, v___x_1714_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec_ref(v___x_1721_);
return v___x_1725_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1708_ = stack[0].m_obj;
lean_object* v___x_1709_ = stack[1].m_obj;
lean_object* v_types_1710_ = stack[2].m_obj;
lean_object* v_i_1711_ = stack[3].m_obj;
uint8_t v___x_1712_ = stack[4].m_num;
uint8_t v___x_1713_ = stack[5].m_num;
uint8_t v___x_1714_ = stack[6].m_num;
lean_object* v_x_1715_ = stack[7].m_obj;
lean_object* v___y_1716_ = stack[8].m_obj;
lean_object* v___y_1717_ = stack[9].m_obj;
lean_object* v___y_1718_ = stack[10].m_obj;
lean_object* v___y_1719_ = stack[11].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v___x_1708_, v___x_1709_, v_types_1710_, v_i_1711_, v___x_1712_, v___x_1713_, v___x_1714_, v_x_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
stack->m_obj
 = v_res_1726_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object* v___x_1727_, lean_object* v___x_1728_, lean_object* v_types_1729_, lean_object* v_i_1730_, lean_object* v___x_1731_, lean_object* v___x_1732_, lean_object* v___x_1733_, lean_object* v_x_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_1665__boxed_1740_; uint8_t v___x_1666__boxed_1741_; uint8_t v___x_1667__boxed_1742_; lean_object* v_res_1743_; 
v___x_1665__boxed_1740_ = lean_unbox(v___x_1731_);
v___x_1666__boxed_1741_ = lean_unbox(v___x_1732_);
v___x_1667__boxed_1742_ = lean_unbox(v___x_1733_);
v_res_1743_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v___x_1727_, v___x_1728_, v_types_1729_, v_i_1730_, v___x_1665__boxed_1740_, v___x_1666__boxed_1741_, v___x_1667__boxed_1742_, v_x_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v_i_1730_);
lean_dec_ref(v_types_1729_);
lean_dec_ref(v___x_1728_);
return v_res_1743_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1746_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1));
v___x_1747_ = lean_unsigned_to_nat(6u);
v___x_1748_ = lean_unsigned_to_nat(318u);
v___x_1749_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0));
v___x_1750_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1751_ = l_mkPanicMessageWithDecl(v___x_1750_, v___x_1749_, v___x_1748_, v___x_1747_, v___x_1746_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object* v_i_1755_, lean_object* v___x_1756_, lean_object* v_types_1757_, lean_object* v_u_1758_, lean_object* v___x_1759_, lean_object* v___x_1760_, lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v_x_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v___x_1750__boxed_1769_; uint8_t v___x_1751__boxed_1770_; uint8_t v___x_1752__boxed_1771_; lean_object* v_res_1772_; 
v___x_1750__boxed_1769_ = lean_unbox(v___x_1760_);
v___x_1751__boxed_1770_ = lean_unbox(v___x_1761_);
v___x_1752__boxed_1771_ = lean_unbox(v___x_1762_);
v_res_1772_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_i_1755_, v___x_1756_, v_types_1757_, v_u_1758_, v___x_1759_, v___x_1750__boxed_1769_, v___x_1751__boxed_1770_, v___x_1752__boxed_1771_, v_x_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___x_1756_);
lean_dec(v_i_1755_);
return v_res_1772_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object* v_types_1773_, lean_object* v_u_1774_, lean_object* v_x_1775_, lean_object* v_i_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1782_ = l_Lean_instInhabitedExpr;
v___x_1783_ = lean_array_get_size(v_types_1773_);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_nat_sub(v___x_1783_, v___x_1784_);
v___x_1786_ = lean_nat_dec_lt(v_i_1776_, v___x_1785_);
lean_dec(v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v_u_1774_);
v___x_1787_ = lean_array_get(v___x_1782_, v_types_1773_, v_i_1776_);
lean_dec(v_i_1776_);
lean_dec_ref(v_types_1773_);
v___x_1788_ = l_Lean_Expr_bindingBody_x21(v___x_1787_);
lean_dec(v___x_1787_);
v___x_1789_ = lean_expr_instantiate1(v___x_1788_, v_x_1775_);
lean_dec_ref(v_x_1775_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; 
lean_inc(v_a_1780_);
lean_inc_ref(v_a_1779_);
lean_inc(v_a_1778_);
lean_inc_ref(v_a_1777_);
lean_inc_ref(v_x_1775_);
v___x_1791_ = lean_infer_type(v_x_1775_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1793_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1793_ = l_Lean_Meta_whnfD(v_a_1792_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_1796_ = lean_unsigned_to_nat(2u);
v___x_1797_ = l_Lean_Expr_isAppOfArity(v_a_1794_, v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v_a_1794_);
lean_dec(v_i_1776_);
lean_dec_ref(v_x_1775_);
lean_dec(v_u_1774_);
lean_dec_ref(v_types_1773_);
v___x_1798_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
v___x_1799_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1798_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_1799_;
}
else
{
lean_object* v_dummy_1800_; lean_object* v_nargs_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___f_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; 
v_dummy_1800_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go___closed__0);
v_nargs_1801_ = l_Lean_Expr_getAppNumArgs(v_a_1794_);
lean_inc(v_nargs_1801_);
v___x_1802_ = lean_mk_array(v_nargs_1801_, v_dummy_1800_);
v___x_1803_ = lean_nat_sub(v_nargs_1801_, v___x_1784_);
lean_dec(v_nargs_1801_);
lean_inc(v_a_1794_);
v___x_1804_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1794_, v___x_1802_, v___x_1803_);
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
lean_inc_n(v_u_1774_, 2);
v___x_1806_ = l_Lean_Level_succ___override(v_u_1774_);
v___x_1807_ = l_Lean_Expr_getAppFn(v_a_1794_);
lean_dec(v_a_1794_);
v___x_1808_ = l_Lean_Expr_constLevels_x21(v___x_1807_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1806_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = l_Lean_mkConst(v___x_1805_, v___x_1809_);
v___x_1811_ = l_Lean_mkAppN(v___x_1810_, v___x_1804_);
v___x_1812_ = lean_mk_empty_array_with_capacity(v___x_1784_);
lean_inc_ref(v_x_1775_);
lean_inc_ref_n(v___x_1812_, 2);
v___x_1813_ = lean_array_push(v___x_1812_, v_x_1775_);
v___x_1814_ = l_Lean_mkSort(v_u_1774_);
v___x_1815_ = 0;
v___x_1816_ = 1;
v___x_1817_ = lean_box(v___x_1815_);
v___x_1818_ = lean_box(v___x_1786_);
v___x_1819_ = lean_box(v___x_1816_);
lean_inc(v_i_1776_);
lean_inc_ref(v_types_1773_);
v___f_1820_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1820_, 0, v___x_1812_);
lean_closure_set(v___f_1820_, 1, v___x_1782_);
lean_closure_set(v___f_1820_, 2, v_types_1773_);
lean_closure_set(v___f_1820_, 3, v_i_1776_);
lean_closure_set(v___f_1820_, 4, v___x_1817_);
lean_closure_set(v___f_1820_, 5, v___x_1818_);
lean_closure_set(v___f_1820_, 6, v___x_1819_);
v___x_1821_ = lean_box(v___x_1815_);
v___x_1822_ = lean_box(v___x_1786_);
v___x_1823_ = lean_box(v___x_1816_);
v___f_1824_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1824_, 0, v_i_1776_);
lean_closure_set(v___f_1824_, 1, v___x_1784_);
lean_closure_set(v___f_1824_, 2, v_types_1773_);
lean_closure_set(v___f_1824_, 3, v_u_1774_);
lean_closure_set(v___f_1824_, 4, v___x_1812_);
lean_closure_set(v___f_1824_, 5, v___x_1821_);
lean_closure_set(v___f_1824_, 6, v___x_1822_);
lean_closure_set(v___f_1824_, 7, v___x_1823_);
v___x_1825_ = l_Lean_Meta_mkLambdaFVars(v___x_1813_, v___x_1814_, v___x_1815_, v___x_1786_, v___x_1815_, v___x_1786_, v___x_1816_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec_ref(v___x_1813_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = l_Lean_Expr_app___override(v___x_1811_, v_a_1826_);
v___x_1828_ = l_Lean_Expr_app___override(v___x_1827_, v_x_1775_);
v___x_1829_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_1830_ = l_Lean_Core_mkFreshUserName(v___x_1829_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1833_ = lean_array_get_borrowed(v___x_1782_, v___x_1804_, v___x_1832_);
lean_inc(v___x_1833_);
v___x_1834_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1831_, v___x_1833_, v___f_1820_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1836_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1836_ = l_Lean_Core_mkFreshUserName(v___x_1829_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = lean_array_get(v___x_1782_, v___x_1804_, v___x_1784_);
lean_dec_ref(v___x_1804_);
v___x_1839_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1837_, v___x_1838_, v___f_1824_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1848_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1844_ = l_Lean_mkAppB(v___x_1828_, v_a_1835_, v_a_1840_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
lean_dec(v_a_1835_);
lean_dec_ref(v___x_1828_);
return v___x_1839_;
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1835_);
lean_dec_ref(v___x_1828_);
lean_dec_ref(v___f_1824_);
lean_dec_ref(v___x_1804_);
v_a_1849_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1836_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1836_);
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
}
else
{
lean_dec_ref(v___x_1828_);
lean_dec_ref(v___f_1824_);
lean_dec_ref(v___x_1804_);
return v___x_1834_;
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v___x_1828_);
lean_dec_ref(v___f_1824_);
lean_dec_ref(v___f_1820_);
lean_dec_ref(v___x_1804_);
v_a_1857_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1830_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1830_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_dec_ref(v___f_1824_);
lean_dec_ref(v___f_1820_);
lean_dec_ref(v___x_1811_);
lean_dec_ref(v___x_1804_);
lean_dec_ref(v_x_1775_);
return v___x_1825_;
}
}
}
else
{
lean_dec(v_i_1776_);
lean_dec_ref(v_x_1775_);
lean_dec(v_u_1774_);
lean_dec_ref(v_types_1773_);
return v___x_1793_;
}
}
else
{
lean_dec(v_i_1776_);
lean_dec_ref(v_x_1775_);
lean_dec(v_u_1774_);
lean_dec_ref(v_types_1773_);
return v___x_1791_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_types_1773_ = stack[0].m_obj;
lean_object* v_u_1774_ = stack[1].m_obj;
lean_object* v_x_1775_ = stack[2].m_obj;
lean_object* v_i_1776_ = stack[3].m_obj;
lean_object* v_a_1777_ = stack[4].m_obj;
lean_object* v_a_1778_ = stack[5].m_obj;
lean_object* v_a_1779_ = stack[6].m_obj;
lean_object* v_a_1780_ = stack[7].m_obj;
lean_object* v_res_1865_;
v_res_1865_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1773_, v_u_1774_, v_x_1775_, v_i_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
stack->m_obj
 = v_res_1865_;
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object* v_i_1866_, lean_object* v___x_1867_, lean_object* v_types_1868_, lean_object* v_u_1869_, lean_object* v___x_1870_, uint8_t v___x_1871_, uint8_t v___x_1872_, uint8_t v___x_1873_, lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_nat_add(v_i_1866_, v___x_1867_);
lean_inc_ref(v_x_1874_);
v___x_1881_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1868_, v_u_1869_, v_x_1874_, v___x_1880_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___x_1883_ = lean_array_push(v___x_1870_, v_x_1874_);
v___x_1884_ = l_Lean_Meta_mkLambdaFVars(v___x_1883_, v_a_1882_, v___x_1871_, v___x_1872_, v___x_1871_, v___x_1872_, v___x_1873_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec_ref(v___x_1883_);
return v___x_1884_;
}
else
{
lean_dec_ref(v_x_1874_);
lean_dec_ref(v___x_1870_);
return v___x_1881_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1866_ = stack[0].m_obj;
lean_object* v___x_1867_ = stack[1].m_obj;
lean_object* v_types_1868_ = stack[2].m_obj;
lean_object* v_u_1869_ = stack[3].m_obj;
lean_object* v___x_1870_ = stack[4].m_obj;
uint8_t v___x_1871_ = stack[5].m_num;
uint8_t v___x_1872_ = stack[6].m_num;
uint8_t v___x_1873_ = stack[7].m_num;
lean_object* v_x_1874_ = stack[8].m_obj;
lean_object* v___y_1875_ = stack[9].m_obj;
lean_object* v___y_1876_ = stack[10].m_obj;
lean_object* v___y_1877_ = stack[11].m_obj;
lean_object* v___y_1878_ = stack[12].m_obj;
lean_object* v_res_1885_;
v_res_1885_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_i_1866_, v___x_1867_, v_types_1868_, v_u_1869_, v___x_1870_, v___x_1871_, v___x_1872_, v___x_1873_, v_x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
stack->m_obj
 = v_res_1885_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object* v_types_1886_, lean_object* v_u_1887_, lean_object* v_x_1888_, lean_object* v_i_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1886_, v_u_1887_, v_x_1888_, v_i_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
return v_res_1895_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object* v_x_1896_, lean_object* v_body_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Meta_getLevel(v_body_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1896_ = stack[0].m_obj;
lean_object* v_body_1897_ = stack[1].m_obj;
lean_object* v___y_1898_ = stack[2].m_obj;
lean_object* v___y_1899_ = stack[3].m_obj;
lean_object* v___y_1900_ = stack[4].m_obj;
lean_object* v___y_1901_ = stack[5].m_obj;
lean_object* v_res_1904_;
v_res_1904_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1896_, v_body_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
stack->m_obj
 = v_res_1904_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object* v_x_1905_, lean_object* v_body_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1905_, v_body_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_x_1905_);
return v_res_1912_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object* v_types_1914_, lean_object* v_x_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___f_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
v___f_1921_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0));
v___x_1922_ = l_Lean_instInhabitedExpr;
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_array_get_borrowed(v___x_1922_, v_types_1914_, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1926_ = 0;
lean_inc(v___x_1924_);
v___x_1927_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_1924_, v___x_1925_, v___f_1921_, v___x_1926_, v___x_1926_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_types_1914_, v_a_1928_, v_x_1915_, v___x_1923_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
return v___x_1929_;
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_x_1915_);
lean_dec_ref(v_types_1914_);
v_a_1930_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1927_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1927_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_mkCodomain_0interp(lean_interpreter_value* stack)
{
lean_object* v_types_1914_ = stack[0].m_obj;
lean_object* v_x_1915_ = stack[1].m_obj;
lean_object* v_a_1916_ = stack[2].m_obj;
lean_object* v_a_1917_ = stack[3].m_obj;
lean_object* v_a_1918_ = stack[4].m_obj;
lean_object* v_a_1919_ = stack[5].m_obj;
lean_object* v_res_1938_;
v_res_1938_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1914_, v_x_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
stack->m_obj
 = v_res_1938_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object* v_types_1939_, lean_object* v_x_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1939_, v_x_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec_ref(v_a_1941_);
return v_res_1946_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object* v_a_1947_, lean_object* v___x_1948_, uint8_t v___x_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
lean_inc_ref(v_x_1950_);
v___x_1956_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_a_1947_, v_x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = lean_mk_empty_array_with_capacity(v___x_1948_);
v___x_1959_ = lean_array_push(v___x_1958_, v_x_1950_);
v___x_1960_ = 1;
v___x_1961_ = 1;
v___x_1962_ = l_Lean_Meta_mkForallFVars(v___x_1959_, v_a_1957_, v___x_1949_, v___x_1960_, v___x_1960_, v___x_1961_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec_ref(v___x_1959_);
return v___x_1962_;
}
else
{
lean_dec_ref(v_x_1950_);
return v___x_1956_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1947_ = stack[0].m_obj;
lean_object* v___x_1948_ = stack[1].m_obj;
uint8_t v___x_1949_ = stack[2].m_num;
lean_object* v_x_1950_ = stack[3].m_obj;
lean_object* v___y_1951_ = stack[4].m_obj;
lean_object* v___y_1952_ = stack[5].m_obj;
lean_object* v___y_1953_ = stack[6].m_obj;
lean_object* v___y_1954_ = stack[7].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1947_, v___x_1948_, v___x_1949_, v_x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object* v_a_1964_, lean_object* v___x_1965_, lean_object* v___x_1966_, lean_object* v_x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v___x_1818__boxed_1973_; lean_object* v_res_1974_; 
v___x_1818__boxed_1973_ = lean_unbox(v___x_1966_);
v_res_1974_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1964_, v___x_1965_, v___x_1818__boxed_1973_, v_x_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___x_1965_);
return v_res_1974_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t v_sz_1975_, size_t v_i_1976_, lean_object* v_bs_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_usize_dec_lt(v_i_1976_, v_sz_1975_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_bs_1977_);
return v___x_1984_;
}
else
{
lean_object* v_v_1985_; lean_object* v___x_1986_; lean_object* v_bs_x27_1987_; lean_object* v___x_1988_; 
v_v_1985_ = lean_array_uget(v_bs_1977_, v_i_1976_);
v___x_1986_ = lean_unsigned_to_nat(0u);
v_bs_x27_1987_ = lean_array_uset(v_bs_1977_, v_i_1976_, v___x_1986_);
v___x_1988_ = l_Lean_Meta_whnfForall(v_v_1985_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = ((size_t)1ULL);
v___x_1991_ = lean_usize_add(v_i_1976_, v___x_1990_);
v___x_1992_ = lean_array_uset(v_bs_x27_1987_, v_i_1976_, v_a_1989_);
v_i_1976_ = v___x_1991_;
v_bs_1977_ = v___x_1992_;
goto _start;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_bs_x27_1987_);
v_a_1994_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1988_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1988_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1975_ = stack[0].m_num;
size_t v_i_1976_ = stack[1].m_num;
lean_object* v_bs_1977_ = stack[2].m_obj;
lean_object* v___y_1978_ = stack[3].m_obj;
lean_object* v___y_1979_ = stack[4].m_obj;
lean_object* v___y_1980_ = stack[5].m_obj;
lean_object* v___y_1981_ = stack[6].m_obj;
lean_object* v_res_2002_;
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_1975_, v_i_1976_, v_bs_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
stack->m_obj
 = v_res_2002_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object* v_sz_2003_, lean_object* v_i_2004_, lean_object* v_bs_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
size_t v_sz_boxed_2011_; size_t v_i_boxed_2012_; lean_object* v_res_2013_; 
v_sz_boxed_2011_ = lean_unbox_usize(v_sz_2003_);
lean_dec(v_sz_2003_);
v_i_boxed_2012_ = lean_unbox_usize(v_i_2004_);
lean_dec(v_i_2004_);
v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_2011_, v_i_boxed_2012_, v_bs_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2013_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0));
v___x_2016_ = l_Lean_stringToMessageData(v___x_2015_);
return v___x_2016_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object* v_as_2017_, size_t v_i_2018_, size_t v_stop_2019_, lean_object* v_b_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_a_2027_; uint8_t v___x_2031_; 
v___x_2031_ = lean_usize_dec_eq(v_i_2018_, v_stop_2019_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = lean_array_uget_borrowed(v_as_2017_, v_i_2018_);
v___x_2033_ = l_Lean_Expr_isForall(v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2034_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
lean_inc(v___x_2032_);
v___x_2035_ = l_Lean_MessageData_ofExpr(v___x_2032_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2036_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v_a_2027_ = v_a_2038_;
goto v___jp_2026_;
}
else
{
return v___x_2037_;
}
}
else
{
lean_object* v___x_2039_; 
v___x_2039_ = lean_box(0);
v_a_2027_ = v___x_2039_;
goto v___jp_2026_;
}
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_b_2020_);
return v___x_2040_;
}
v___jp_2026_:
{
size_t v___x_2028_; size_t v___x_2029_; 
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_add(v_i_2018_, v___x_2028_);
v_i_2018_ = v___x_2029_;
v_b_2020_ = v_a_2027_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2017_ = stack[0].m_obj;
size_t v_i_2018_ = stack[1].m_num;
size_t v_stop_2019_ = stack[2].m_num;
lean_object* v_b_2020_ = stack[3].m_obj;
lean_object* v___y_2021_ = stack[4].m_obj;
lean_object* v___y_2022_ = stack[5].m_obj;
lean_object* v___y_2023_ = stack[6].m_obj;
lean_object* v___y_2024_ = stack[7].m_obj;
lean_object* v_res_2041_;
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_2017_, v_i_2018_, v_stop_2019_, v_b_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
stack->m_obj
 = v_res_2041_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object* v_as_2042_, lean_object* v_i_2043_, lean_object* v_stop_2044_, lean_object* v_b_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
size_t v_i_boxed_2051_; size_t v_stop_boxed_2052_; lean_object* v_res_2053_; 
v_i_boxed_2051_ = lean_unbox_usize(v_i_2043_);
lean_dec(v_i_2043_);
v_stop_boxed_2052_ = lean_unbox_usize(v_stop_2044_);
lean_dec(v_stop_2044_);
v_res_2053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_2042_, v_i_boxed_2051_, v_stop_boxed_2052_, v_b_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec_ref(v_as_2042_);
return v_res_2053_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t v_sz_2054_, size_t v_i_2055_, lean_object* v_bs_2056_){
_start:
{
uint8_t v___x_2057_; 
v___x_2057_ = lean_usize_dec_lt(v_i_2055_, v_sz_2054_);
if (v___x_2057_ == 0)
{
return v_bs_2056_;
}
else
{
lean_object* v_v_2058_; lean_object* v___x_2059_; lean_object* v_bs_x27_2060_; lean_object* v___x_2061_; size_t v___x_2062_; size_t v___x_2063_; lean_object* v___x_2064_; 
v_v_2058_ = lean_array_uget(v_bs_2056_, v_i_2055_);
v___x_2059_ = lean_unsigned_to_nat(0u);
v_bs_x27_2060_ = lean_array_uset(v_bs_2056_, v_i_2055_, v___x_2059_);
v___x_2061_ = l_Lean_Expr_bindingDomain_x21(v_v_2058_);
lean_dec(v_v_2058_);
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = lean_usize_add(v_i_2055_, v___x_2062_);
v___x_2064_ = lean_array_uset(v_bs_x27_2060_, v_i_2055_, v___x_2061_);
v_i_2055_ = v___x_2063_;
v_bs_2056_ = v___x_2064_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2054_ = stack[0].m_num;
size_t v_i_2055_ = stack[1].m_num;
lean_object* v_bs_2056_ = stack[2].m_obj;
lean_object* v_res_2066_;
v_res_2066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_2054_, v_i_2055_, v_bs_2056_);
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object* v_sz_2067_, lean_object* v_i_2068_, lean_object* v_bs_2069_){
_start:
{
size_t v_sz_boxed_2070_; size_t v_i_boxed_2071_; lean_object* v_res_2072_; 
v_sz_boxed_2070_ = lean_unbox_usize(v_sz_2067_);
lean_dec(v_sz_2067_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2068_);
lean_dec(v_i_2068_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_2070_, v_i_boxed_2071_, v_bs_2069_);
return v_res_2072_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object* v_types_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2079_ = lean_array_get_size(v_types_2073_);
v___x_2080_ = lean_unsigned_to_nat(1u);
v___x_2081_ = lean_nat_dec_eq(v___x_2079_, v___x_2080_);
if (v___x_2081_ == 0)
{
size_t v_sz_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v_sz_2082_ = lean_array_size(v_types_2073_);
v___x_2083_ = ((size_t)0ULL);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2082_, v___x_2083_, v_types_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; lean_object* v___f_2087_; lean_object* v___y_2106_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc_n(v_a_2085_, 2);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = lean_box(v___x_2081_);
v___f_2087_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2087_, 0, v_a_2085_);
lean_closure_set(v___f_2087_, 1, v___x_2080_);
lean_closure_set(v___f_2087_, 2, v___x_2086_);
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_array_get_size(v_a_2085_);
v___x_2117_ = lean_nat_dec_lt(v___x_2115_, v___x_2116_);
if (v___x_2117_ == 0)
{
goto v___jp_2088_;
}
else
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = lean_box(0);
v___x_2119_ = lean_nat_dec_le(v___x_2116_, v___x_2116_);
if (v___x_2119_ == 0)
{
if (v___x_2117_ == 0)
{
goto v___jp_2088_;
}
else
{
size_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_usize_of_nat(v___x_2116_);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2085_, v___x_2083_, v___x_2120_, v___x_2118_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
v___y_2106_ = v___x_2121_;
goto v___jp_2105_;
}
}
else
{
size_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_usize_of_nat(v___x_2116_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_2085_, v___x_2083_, v___x_2122_, v___x_2118_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
v___y_2106_ = v___x_2123_;
goto v___jp_2105_;
}
}
v___jp_2088_:
{
size_t v_sz_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_sz_2089_ = lean_array_size(v_a_2085_);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_2089_, v___x_2083_, v_a_2085_);
v___x_2091_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2090_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2094_ = l_Lean_Core_mkFreshUserName(v___x_2093_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2095_, v_a_2092_, v___f_2087_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
return v___x_2096_;
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_a_2092_);
lean_dec_ref(v___f_2087_);
v_a_2097_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2094_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2094_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_dec_ref(v___f_2087_);
return v___x_2091_;
}
}
v___jp_2105_:
{
if (lean_obj_tag(v___y_2106_) == 0)
{
lean_dec_ref_known(v___y_2106_, 1);
goto v___jp_2088_;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v___f_2087_);
lean_dec(v_a_2085_);
v_a_2107_ = lean_ctor_get(v___y_2106_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___y_2106_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___y_2106_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___y_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
v_a_2124_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2084_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2084_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2132_ = l_Lean_instInhabitedExpr;
v___x_2133_ = lean_unsigned_to_nat(0u);
v___x_2134_ = lean_array_get(v___x_2132_, v_types_2073_, v___x_2133_);
lean_dec_ref(v_types_2073_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
return v___x_2135_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_uncurryType_0interp(lean_interpreter_value* stack)
{
lean_object* v_types_2073_ = stack[0].m_obj;
lean_object* v_a_2074_ = stack[1].m_obj;
lean_object* v_a_2075_ = stack[2].m_obj;
lean_object* v_a_2076_ = stack[3].m_obj;
lean_object* v_a_2077_ = stack[4].m_obj;
lean_object* v_res_2136_;
v_res_2136_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
stack->m_obj
 = v_res_2136_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object* v_types_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
return v_res_2143_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object* v___x_2150_, lean_object* v_as_2151_, size_t v_i_2152_, size_t v_stop_2153_, lean_object* v_b_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_a_2161_; uint8_t v___x_2165_; 
v___x_2165_ = lean_usize_dec_eq(v_i_2152_, v_stop_2153_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_array_uget_borrowed(v_as_2151_, v_i_2152_);
lean_inc_ref(v___x_2150_);
lean_inc(v___x_2166_);
v___x_2167_ = l_Lean_Meta_isExprDefEq(v___x_2166_, v___x_2150_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; uint8_t v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = lean_unbox(v_a_2168_);
lean_dec(v_a_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2170_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
lean_inc(v___x_2166_);
v___x_2171_ = l_Lean_MessageData_ofExpr(v___x_2166_);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
lean_inc_ref(v___x_2150_);
v___x_2175_ = l_Lean_MessageData_ofExpr(v___x_2150_);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2176_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v_a_2161_ = v_a_2178_;
goto v___jp_2160_;
}
else
{
lean_dec_ref(v___x_2150_);
return v___x_2177_;
}
}
else
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_box(0);
v_a_2161_ = v___x_2179_;
goto v___jp_2160_;
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v___x_2150_);
v_a_2180_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2167_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2167_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v___x_2188_; 
lean_dec_ref(v___x_2150_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_b_2154_);
return v___x_2188_;
}
v___jp_2160_:
{
size_t v___x_2162_; size_t v___x_2163_; 
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2152_, v___x_2162_);
v_i_2152_ = v___x_2163_;
v_b_2154_ = v_a_2161_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2150_ = stack[0].m_obj;
lean_object* v_as_2151_ = stack[1].m_obj;
size_t v_i_2152_ = stack[2].m_num;
size_t v_stop_2153_ = stack[3].m_num;
lean_object* v_b_2154_ = stack[4].m_obj;
lean_object* v___y_2155_ = stack[5].m_obj;
lean_object* v___y_2156_ = stack[6].m_obj;
lean_object* v___y_2157_ = stack[7].m_obj;
lean_object* v___y_2158_ = stack[8].m_obj;
lean_object* v_res_2189_;
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2150_, v_as_2151_, v_i_2152_, v_stop_2153_, v_b_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
stack->m_obj
 = v_res_2189_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object* v___x_2190_, lean_object* v_as_2191_, lean_object* v_i_2192_, lean_object* v_stop_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
size_t v_i_boxed_2200_; size_t v_stop_boxed_2201_; lean_object* v_res_2202_; 
v_i_boxed_2200_ = lean_unbox_usize(v_i_2192_);
lean_dec(v_i_2192_);
v_stop_boxed_2201_ = lean_unbox_usize(v_stop_2193_);
lean_dec(v_stop_2193_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2190_, v_as_2191_, v_i_boxed_2200_, v_stop_boxed_2201_, v_b_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v_as_2191_);
return v_res_2202_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t v_sz_2203_, size_t v_i_2204_, lean_object* v_bs_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_usize_dec_lt(v_i_2204_, v_sz_2203_);
if (v___x_2206_ == 0)
{
return v_bs_2205_;
}
else
{
lean_object* v_v_2207_; lean_object* v___x_2208_; lean_object* v_bs_x27_2209_; lean_object* v___x_2210_; size_t v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v_v_2207_ = lean_array_uget(v_bs_2205_, v_i_2204_);
v___x_2208_ = lean_unsigned_to_nat(0u);
v_bs_x27_2209_ = lean_array_uset(v_bs_2205_, v_i_2204_, v___x_2208_);
v___x_2210_ = l_Lean_Expr_bindingBody_x21(v_v_2207_);
lean_dec(v_v_2207_);
v___x_2211_ = ((size_t)1ULL);
v___x_2212_ = lean_usize_add(v_i_2204_, v___x_2211_);
v___x_2213_ = lean_array_uset(v_bs_x27_2209_, v_i_2204_, v___x_2210_);
v_i_2204_ = v___x_2212_;
v_bs_2205_ = v___x_2213_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2203_ = stack[0].m_num;
size_t v_i_2204_ = stack[1].m_num;
lean_object* v_bs_2205_ = stack[2].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2203_, v_i_2204_, v_bs_2205_);
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object* v_sz_2216_, lean_object* v_i_2217_, lean_object* v_bs_2218_){
_start:
{
size_t v_sz_boxed_2219_; size_t v_i_boxed_2220_; lean_object* v_res_2221_; 
v_sz_boxed_2219_ = lean_unbox_usize(v_sz_2216_);
lean_dec(v_sz_2216_);
v_i_boxed_2220_ = lean_unbox_usize(v_i_2217_);
lean_dec(v_i_2217_);
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_2219_, v_i_boxed_2220_, v_bs_2218_);
return v_res_2221_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object* v_as_2225_, size_t v_i_2226_, size_t v_stop_2227_, lean_object* v_b_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_a_2235_; uint8_t v___x_2239_; 
v___x_2239_ = lean_usize_dec_eq(v_i_2226_, v_stop_2227_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_array_uget_borrowed(v_as_2225_, v_i_2226_);
v___x_2241_ = l_Lean_Expr_isArrow(v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2242_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
lean_inc(v___x_2240_);
v___x_2243_ = l_Lean_MessageData_ofExpr(v___x_2240_);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2244_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v_a_2235_ = v_a_2246_;
goto v___jp_2234_;
}
else
{
return v___x_2245_;
}
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_box(0);
v_a_2235_ = v___x_2247_;
goto v___jp_2234_;
}
}
else
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_b_2228_);
return v___x_2248_;
}
v___jp_2234_:
{
size_t v___x_2236_; size_t v___x_2237_; 
v___x_2236_ = ((size_t)1ULL);
v___x_2237_ = lean_usize_add(v_i_2226_, v___x_2236_);
v_i_2226_ = v___x_2237_;
v_b_2228_ = v_a_2235_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2225_ = stack[0].m_obj;
size_t v_i_2226_ = stack[1].m_num;
size_t v_stop_2227_ = stack[2].m_num;
lean_object* v_b_2228_ = stack[3].m_obj;
lean_object* v___y_2229_ = stack[4].m_obj;
lean_object* v___y_2230_ = stack[5].m_obj;
lean_object* v___y_2231_ = stack[6].m_obj;
lean_object* v___y_2232_ = stack[7].m_obj;
lean_object* v_res_2249_;
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2225_, v_i_2226_, v_stop_2227_, v_b_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
stack->m_obj
 = v_res_2249_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object* v_as_2250_, lean_object* v_i_2251_, lean_object* v_stop_2252_, lean_object* v_b_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
size_t v_i_boxed_2259_; size_t v_stop_boxed_2260_; lean_object* v_res_2261_; 
v_i_boxed_2259_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_stop_boxed_2260_ = lean_unbox_usize(v_stop_2252_);
lean_dec(v_stop_2252_);
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2250_, v_i_boxed_2259_, v_stop_boxed_2260_, v_b_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_as_2250_);
return v_res_2261_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object* v_types_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2268_; size_t v_sz_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
v___x_2268_ = l_Lean_instInhabitedExpr;
v_sz_2269_ = lean_array_size(v_types_2262_);
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2269_, v___x_2270_, v_types_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; size_t v___y_2275_; lean_object* v___y_2276_; size_t v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2311_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2320_ = lean_array_get_size(v_a_2272_);
v___x_2321_ = lean_nat_dec_lt(v___x_2273_, v___x_2320_);
if (v___x_2321_ == 0)
{
goto v___jp_2294_;
}
else
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_nat_dec_le(v___x_2320_, v___x_2320_);
if (v___x_2323_ == 0)
{
if (v___x_2321_ == 0)
{
goto v___jp_2294_;
}
else
{
size_t v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_usize_of_nat(v___x_2320_);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2272_, v___x_2270_, v___x_2324_, v___x_2322_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
v___y_2311_ = v___x_2325_;
goto v___jp_2310_;
}
}
else
{
size_t v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_usize_of_nat(v___x_2320_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2272_, v___x_2270_, v___x_2326_, v___x_2322_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
v___y_2311_ = v___x_2327_;
goto v___jp_2310_;
}
}
v___jp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_array_get(v___x_2268_, v___y_2276_, v___x_2273_);
lean_dec_ref(v___y_2276_);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_2275_, v___x_2270_, v_a_2272_);
v___x_2279_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2278_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = l_Lean_mkArrow(v_a_2280_, v___x_2277_, v_a_2265_, v_a_2266_);
return v___x_2281_;
}
else
{
lean_dec(v___x_2277_);
return v___x_2279_;
}
}
v___jp_2282_:
{
if (lean_obj_tag(v___y_2285_) == 0)
{
lean_dec_ref_known(v___y_2285_, 1);
v___y_2275_ = v___y_2283_;
v___y_2276_ = v___y_2284_;
goto v___jp_2274_;
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v___y_2284_);
lean_dec(v_a_2272_);
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
v___jp_2294_:
{
size_t v_sz_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_sz_2295_ = lean_array_size(v_a_2272_);
lean_inc(v_a_2272_);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2295_, v___x_2270_, v_a_2272_);
v___x_2297_ = lean_array_get_size(v___x_2296_);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_sub(v___x_2297_, v___x_2298_);
v___x_2300_ = lean_array_get_borrowed(v___x_2268_, v___x_2296_, v___x_2299_);
lean_dec(v___x_2299_);
lean_inc_ref(v___x_2296_);
v___x_2301_ = lean_array_pop(v___x_2296_);
v___x_2302_ = lean_array_get_size(v___x_2301_);
v___x_2303_ = lean_nat_dec_lt(v___x_2273_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_dec_ref(v___x_2301_);
v___y_2275_ = v_sz_2295_;
v___y_2276_ = v___x_2296_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = lean_box(0);
v___x_2305_ = lean_nat_dec_le(v___x_2302_, v___x_2302_);
if (v___x_2305_ == 0)
{
if (v___x_2303_ == 0)
{
lean_dec_ref(v___x_2301_);
v___y_2275_ = v_sz_2295_;
v___y_2276_ = v___x_2296_;
goto v___jp_2274_;
}
else
{
size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_usize_of_nat(v___x_2302_);
lean_inc(v___x_2300_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2300_, v___x_2301_, v___x_2270_, v___x_2306_, v___x_2304_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec_ref(v___x_2301_);
v___y_2283_ = v_sz_2295_;
v___y_2284_ = v___x_2296_;
v___y_2285_ = v___x_2307_;
goto v___jp_2282_;
}
}
else
{
size_t v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_usize_of_nat(v___x_2302_);
lean_inc(v___x_2300_);
v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2300_, v___x_2301_, v___x_2270_, v___x_2308_, v___x_2304_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec_ref(v___x_2301_);
v___y_2283_ = v_sz_2295_;
v___y_2284_ = v___x_2296_;
v___y_2285_ = v___x_2309_;
goto v___jp_2282_;
}
}
}
v___jp_2310_:
{
if (lean_obj_tag(v___y_2311_) == 0)
{
lean_dec_ref_known(v___y_2311_, 1);
goto v___jp_2294_;
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec(v_a_2272_);
v_a_2312_ = lean_ctor_get(v___y_2311_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___y_2311_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___y_2311_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___y_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
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
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
v_a_2328_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2271_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2271_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_0interp(lean_interpreter_value* stack)
{
lean_object* v_types_2262_ = stack[0].m_obj;
lean_object* v_a_2263_ = stack[1].m_obj;
lean_object* v_a_2264_ = stack[2].m_obj;
lean_object* v_a_2265_ = stack[3].m_obj;
lean_object* v_a_2266_ = stack[4].m_obj;
lean_object* v_res_2336_;
v_res_2336_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
stack->m_obj
 = v_res_2336_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object* v_types_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
return v_res_2343_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0));
v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
return v___x_2346_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2));
v___x_2349_ = l_Lean_stringToMessageData(v___x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object* v___x_2350_, lean_object* v___x_2351_, lean_object* v_arg_2352_, lean_object* v_arg_2353_, lean_object* v___x_2354_, lean_object* v_a_2355_, lean_object* v_tail_2356_, lean_object* v___x_2357_, lean_object* v___x_2358_, lean_object* v___x_2359_, lean_object* v_y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
uint8_t v___x_2270__boxed_2366_; uint8_t v___x_2271__boxed_2367_; uint8_t v___x_2272__boxed_2368_; lean_object* v_res_2369_; 
v___x_2270__boxed_2366_ = lean_unbox(v___x_2357_);
v___x_2271__boxed_2367_ = lean_unbox(v___x_2358_);
v___x_2272__boxed_2368_ = lean_unbox(v___x_2359_);
v_res_2369_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v___x_2350_, v___x_2351_, v_arg_2352_, v_arg_2353_, v___x_2354_, v_a_2355_, v_tail_2356_, v___x_2270__boxed_2366_, v___x_2271__boxed_2367_, v___x_2272__boxed_2368_, v_y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
return v_res_2369_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object* v_x_2370_, lean_object* v_codomain_2371_, lean_object* v_alts_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
if (lean_obj_tag(v_alts_2372_) == 0)
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec_ref(v_codomain_2371_);
lean_dec_ref(v_x_2370_);
v___x_2378_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
v___x_2379_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2378_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2379_;
}
else
{
lean_object* v_tail_2380_; 
v_tail_2380_ = lean_ctor_get(v_alts_2372_, 1);
if (lean_obj_tag(v_tail_2380_) == 0)
{
lean_object* v_head_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_codomain_2371_);
v_head_2381_ = lean_ctor_get(v_alts_2372_, 0);
lean_inc(v_head_2381_);
lean_dec_ref_known(v_alts_2372_, 2);
v___x_2382_ = lean_unsigned_to_nat(1u);
v___x_2383_ = lean_mk_empty_array_with_capacity(v___x_2382_);
v___x_2384_ = lean_array_push(v___x_2383_, v_x_2370_);
v___x_2385_ = l_Lean_Expr_beta(v_head_2381_, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
else
{
lean_object* v_head_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2472_; 
lean_inc(v_tail_2380_);
v_head_2387_ = lean_ctor_get(v_alts_2372_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_alts_2372_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v_alts_2372_, 1);
lean_dec(v_unused_2473_);
v___x_2389_ = v_alts_2372_;
v_isShared_2390_ = v_isSharedCheck_2472_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_head_2387_);
lean_dec(v_alts_2372_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2472_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; 
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
lean_inc(v_a_2374_);
lean_inc_ref(v_a_2373_);
lean_inc_ref(v_x_2370_);
v___x_2391_ = lean_infer_type(v_x_2370_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___x_2402_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc_n(v_a_2392_, 2);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2402_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2392_, v_a_2374_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = l_Lean_Expr_cleanupAnnotations(v_a_2403_);
v___x_2405_ = l_Lean_Expr_isApp(v___x_2404_);
if (v___x_2405_ == 0)
{
lean_dec_ref(v___x_2404_);
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec(v_tail_2380_);
lean_dec_ref(v_codomain_2371_);
lean_dec_ref(v_x_2370_);
v___y_2394_ = v_a_2373_;
v___y_2395_ = v_a_2374_;
v___y_2396_ = v_a_2375_;
v___y_2397_ = v_a_2376_;
goto v___jp_2393_;
}
else
{
lean_object* v_arg_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v_arg_2406_ = lean_ctor_get(v___x_2404_, 1);
lean_inc_ref(v_arg_2406_);
v___x_2407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2404_);
v___x_2408_ = l_Lean_Expr_isApp(v___x_2407_);
if (v___x_2408_ == 0)
{
lean_dec_ref(v___x_2407_);
lean_dec_ref(v_arg_2406_);
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec(v_tail_2380_);
lean_dec_ref(v_codomain_2371_);
lean_dec_ref(v_x_2370_);
v___y_2394_ = v_a_2373_;
v___y_2395_ = v_a_2374_;
v___y_2396_ = v_a_2375_;
v___y_2397_ = v_a_2376_;
goto v___jp_2393_;
}
else
{
lean_object* v_arg_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v_arg_2409_ = lean_ctor_get(v___x_2407_, 1);
lean_inc_ref(v_arg_2409_);
v___x_2410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2407_);
v___x_2411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__0));
v___x_2412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Mutual_packType_spec__0___closed__1));
v___x_2413_ = l_Lean_Expr_isConstOf(v___x_2410_, v___x_2412_);
lean_dec_ref(v___x_2410_);
if (v___x_2413_ == 0)
{
lean_dec_ref(v_arg_2409_);
lean_dec_ref(v_arg_2406_);
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec(v_tail_2380_);
lean_dec_ref(v_codomain_2371_);
lean_dec_ref(v_x_2370_);
v___y_2394_ = v_a_2373_;
v___y_2395_ = v_a_2374_;
v___y_2396_ = v_a_2375_;
v___y_2397_ = v_a_2376_;
goto v___jp_2393_;
}
else
{
lean_object* v___x_2414_; 
lean_inc_ref(v_codomain_2371_);
v___x_2414_ = l_Lean_Meta_getLevel(v_codomain_2371_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___x_2416_ = l_Lean_Expr_getAppFn(v_a_2392_);
lean_dec(v_a_2392_);
v___x_2417_ = l_Lean_Expr_constLevels_x21(v___x_2416_);
lean_dec_ref(v___x_2416_);
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_mk_empty_array_with_capacity(v___x_2418_);
lean_inc_ref(v_x_2370_);
lean_inc_ref(v___x_2419_);
v___x_2420_ = lean_array_push(v___x_2419_, v_x_2370_);
v___x_2421_ = 0;
v___x_2422_ = 1;
v___x_2423_ = l_Lean_Meta_mkLambdaFVars(v___x_2420_, v_codomain_2371_, v___x_2421_, v___x_2413_, v___x_2421_, v___x_2413_, v___x_2422_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec_ref(v___x_2420_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2463_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2463_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2463_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_alt_u2082_2429_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___f_2442_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; 
v___x_2439_ = lean_box(v___x_2421_);
v___x_2440_ = lean_box(v___x_2413_);
v___x_2441_ = lean_box(v___x_2422_);
lean_inc(v_tail_2380_);
lean_inc(v_a_2424_);
lean_inc_ref(v_arg_2406_);
lean_inc_ref(v_arg_2409_);
lean_inc(v___x_2417_);
v___f_2442_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2442_, 0, v___x_2411_);
lean_closure_set(v___f_2442_, 1, v___x_2417_);
lean_closure_set(v___f_2442_, 2, v_arg_2409_);
lean_closure_set(v___f_2442_, 3, v_arg_2406_);
lean_closure_set(v___f_2442_, 4, v___x_2419_);
lean_closure_set(v___f_2442_, 5, v_a_2424_);
lean_closure_set(v___f_2442_, 6, v_tail_2380_);
lean_closure_set(v___f_2442_, 7, v___x_2439_);
lean_closure_set(v___f_2442_, 8, v___x_2440_);
lean_closure_set(v___f_2442_, 9, v___x_2441_);
if (lean_obj_tag(v_tail_2380_) == 1)
{
lean_object* v_tail_2461_; 
v_tail_2461_ = lean_ctor_get(v_tail_2380_, 1);
if (lean_obj_tag(v_tail_2461_) == 0)
{
lean_object* v_head_2462_; 
lean_dec_ref(v___f_2442_);
v_head_2462_ = lean_ctor_get(v_tail_2380_, 0);
lean_inc(v_head_2462_);
lean_dec_ref_known(v_tail_2380_, 2);
v_alt_u2082_2429_ = v_head_2462_;
goto v___jp_2428_;
}
else
{
lean_dec_ref_known(v_tail_2380_, 2);
v___y_2444_ = v_a_2373_;
v___y_2445_ = v_a_2374_;
v___y_2446_ = v_a_2375_;
v___y_2447_ = v_a_2376_;
goto v___jp_2443_;
}
}
else
{
lean_dec(v_tail_2380_);
v___y_2444_ = v_a_2373_;
v___y_2445_ = v_a_2374_;
v___y_2446_ = v_a_2375_;
v___y_2447_ = v_a_2376_;
goto v___jp_2443_;
}
v___jp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 1, v___x_2417_);
lean_ctor_set(v___x_2389_, 0, v_a_2415_);
v___x_2432_ = v___x_2389_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2415_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2417_);
v___x_2432_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2433_ = l_Lean_Expr_const___override(v___x_2430_, v___x_2432_);
v___x_2434_ = l_Lean_mkApp6(v___x_2433_, v_arg_2409_, v_arg_2406_, v_a_2424_, v_x_2370_, v_head_2387_, v_alt_u2082_2429_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2434_);
v___x_2436_ = v___x_2426_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
v___jp_2443_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_2449_ = l_Lean_Core_mkFreshUserName(v___x_2448_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2451_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
lean_inc_ref(v_arg_2406_);
v___x_2451_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2450_, v_arg_2406_, v___f_2442_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v_alt_u2082_2429_ = v_a_2452_;
goto v___jp_2428_;
}
else
{
lean_del_object(v___x_2426_);
lean_dec(v_a_2424_);
lean_dec(v___x_2417_);
lean_dec(v_a_2415_);
lean_dec_ref(v_arg_2409_);
lean_dec_ref(v_arg_2406_);
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec_ref(v_x_2370_);
return v___x_2451_;
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v___f_2442_);
lean_del_object(v___x_2426_);
lean_dec(v_a_2424_);
lean_dec(v___x_2417_);
lean_dec(v_a_2415_);
lean_dec_ref(v_arg_2409_);
lean_dec_ref(v_arg_2406_);
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec_ref(v_x_2370_);
v_a_2453_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2449_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2449_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2419_);
lean_dec(v___x_2417_);
lean_dec(v_a_2415_);
lean_dec_ref(v_arg_2409_);
lean_dec_ref(v_arg_2406_);
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec(v_tail_2380_);
lean_dec_ref(v_x_2370_);
return v___x_2423_;
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v_arg_2409_);
lean_dec_ref(v_arg_2406_);
lean_dec(v_a_2392_);
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec(v_tail_2380_);
lean_dec_ref(v_codomain_2371_);
lean_dec_ref(v_x_2370_);
v_a_2464_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2414_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2414_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2392_);
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec(v_tail_2380_);
lean_dec_ref(v_codomain_2371_);
lean_dec_ref(v_x_2370_);
return v___x_2402_;
}
v___jp_2393_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2398_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
v___x_2399_ = l_Lean_MessageData_ofExpr(v_a_2392_);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2400_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
return v___x_2401_;
}
}
else
{
lean_del_object(v___x_2389_);
lean_dec(v_head_2387_);
lean_dec(v_tail_2380_);
lean_dec_ref(v_codomain_2371_);
lean_dec_ref(v_x_2370_);
return v___x_2391_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2370_ = stack[0].m_obj;
lean_object* v_codomain_2371_ = stack[1].m_obj;
lean_object* v_alts_2372_ = stack[2].m_obj;
lean_object* v_a_2373_ = stack[3].m_obj;
lean_object* v_a_2374_ = stack[4].m_obj;
lean_object* v_a_2375_ = stack[5].m_obj;
lean_object* v_a_2376_ = stack[6].m_obj;
lean_object* v_res_2474_;
v_res_2474_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2370_, v_codomain_2371_, v_alts_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
stack->m_obj
 = v_res_2474_;
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object* v___x_2475_, lean_object* v___x_2476_, lean_object* v_arg_2477_, lean_object* v_arg_2478_, lean_object* v___x_2479_, lean_object* v_a_2480_, lean_object* v_tail_2481_, uint8_t v___x_2482_, uint8_t v___x_2483_, uint8_t v___x_2484_, lean_object* v_y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2491_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_pack_go_spec__0___closed__3));
v___x_2492_ = l_Lean_Name_mkStr2(v___x_2475_, v___x_2491_);
v___x_2493_ = l_Lean_Expr_const___override(v___x_2492_, v___x_2476_);
lean_inc_ref_n(v_y_2485_, 2);
v___x_2494_ = l_Lean_mkApp3(v___x_2493_, v_arg_2477_, v_arg_2478_, v_y_2485_);
lean_inc_ref(v___x_2479_);
v___x_2495_ = lean_array_push(v___x_2479_, v___x_2494_);
v___x_2496_ = l_Lean_Expr_beta(v_a_2480_, v___x_2495_);
v___x_2497_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_y_2485_, v___x_2496_, v_tail_2481_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = lean_array_push(v___x_2479_, v_y_2485_);
v___x_2500_ = l_Lean_Meta_mkLambdaFVars(v___x_2499_, v_a_2498_, v___x_2482_, v___x_2483_, v___x_2482_, v___x_2483_, v___x_2484_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec_ref(v___x_2499_);
return v___x_2500_;
}
else
{
lean_dec_ref(v_y_2485_);
lean_dec_ref(v___x_2479_);
return v___x_2497_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2475_ = stack[0].m_obj;
lean_object* v___x_2476_ = stack[1].m_obj;
lean_object* v_arg_2477_ = stack[2].m_obj;
lean_object* v_arg_2478_ = stack[3].m_obj;
lean_object* v___x_2479_ = stack[4].m_obj;
lean_object* v_a_2480_ = stack[5].m_obj;
lean_object* v_tail_2481_ = stack[6].m_obj;
uint8_t v___x_2482_ = stack[7].m_num;
uint8_t v___x_2483_ = stack[8].m_num;
uint8_t v___x_2484_ = stack[9].m_num;
lean_object* v_y_2485_ = stack[10].m_obj;
lean_object* v___y_2486_ = stack[11].m_obj;
lean_object* v___y_2487_ = stack[12].m_obj;
lean_object* v___y_2488_ = stack[13].m_obj;
lean_object* v___y_2489_ = stack[14].m_obj;
lean_object* v_res_2501_;
v_res_2501_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v___x_2475_, v___x_2476_, v_arg_2477_, v_arg_2478_, v___x_2479_, v_a_2480_, v_tail_2481_, v___x_2482_, v___x_2483_, v___x_2484_, v_y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
stack->m_obj
 = v_res_2501_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object* v_x_2502_, lean_object* v_codomain_2503_, lean_object* v_alts_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2502_, v_codomain_2503_, v_alts_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
return v_res_2510_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2512_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2513_ = lean_unsigned_to_nat(21u);
v___x_2514_ = lean_unsigned_to_nat(414u);
v___x_2515_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0));
v___x_2516_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2517_ = l_mkPanicMessageWithDecl(v___x_2516_, v___x_2515_, v___x_2514_, v___x_2513_, v___x_2512_);
return v___x_2517_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object* v___x_2518_, lean_object* v_es_2519_, lean_object* v_xs_2520_, lean_object* v_codomain_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = lean_array_get_size(v_xs_2520_);
v___x_2528_ = lean_nat_dec_eq(v___x_2527_, v___x_2518_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec_ref(v_codomain_2521_);
lean_dec_ref(v_es_2519_);
v___x_2529_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1);
v___x_2530_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2529_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = lean_array_fget_borrowed(v_xs_2520_, v___x_2531_);
v___x_2533_ = lean_array_to_list(v_es_2519_);
lean_inc(v___x_2532_);
v___x_2534_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2532_, v_codomain_2521_, v___x_2533_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v___x_2536_ = lean_mk_empty_array_with_capacity(v___x_2518_);
lean_inc(v___x_2532_);
v___x_2537_ = lean_array_push(v___x_2536_, v___x_2532_);
v___x_2538_ = 0;
v___x_2539_ = 1;
v___x_2540_ = l_Lean_Meta_mkLambdaFVars(v___x_2537_, v_a_2535_, v___x_2538_, v___x_2528_, v___x_2538_, v___x_2528_, v___x_2539_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec_ref(v___x_2537_);
return v___x_2540_;
}
else
{
return v___x_2534_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2518_ = stack[0].m_obj;
lean_object* v_es_2519_ = stack[1].m_obj;
lean_object* v_xs_2520_ = stack[2].m_obj;
lean_object* v_codomain_2521_ = stack[3].m_obj;
lean_object* v___y_2522_ = stack[4].m_obj;
lean_object* v___y_2523_ = stack[5].m_obj;
lean_object* v___y_2524_ = stack[6].m_obj;
lean_object* v___y_2525_ = stack[7].m_obj;
lean_object* v_res_2541_;
v_res_2541_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(v___x_2518_, v_es_2519_, v_xs_2520_, v_codomain_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
stack->m_obj
 = v_res_2541_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(lean_object* v___x_2542_, lean_object* v_es_2543_, lean_object* v_xs_2544_, lean_object* v_codomain_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(v___x_2542_, v_es_2543_, v_xs_2544_, v_codomain_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v_xs_2544_);
lean_dec(v___x_2542_);
return v_res_2551_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(lean_object* v_resultType_2552_, lean_object* v_es_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v___f_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; 
v___x_2559_ = lean_unsigned_to_nat(1u);
v___f_2560_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2560_, 0, v___x_2559_);
lean_closure_set(v___f_2560_, 1, v_es_2553_);
v___x_2561_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2562_ = 0;
v___x_2563_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_resultType_2552_, v___x_2561_, v___f_2560_, v___x_2562_, v___x_2562_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
return v___x_2563_;
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType_0interp(lean_interpreter_value* stack)
{
lean_object* v_resultType_2552_ = stack[0].m_obj;
lean_object* v_es_2553_ = stack[1].m_obj;
lean_object* v_a_2554_ = stack[2].m_obj;
lean_object* v_a_2555_ = stack[3].m_obj;
lean_object* v_a_2556_ = stack[4].m_obj;
lean_object* v_a_2557_ = stack[5].m_obj;
lean_object* v_res_2564_;
v_res_2564_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_2552_, v_es_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
stack->m_obj
 = v_res_2564_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(lean_object* v_resultType_2565_, lean_object* v_es_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_2565_, v_es_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
return v_res_2572_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(size_t v_sz_2573_, size_t v_i_2574_, lean_object* v_bs_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
uint8_t v___x_2581_; 
v___x_2581_ = lean_usize_dec_lt(v_i_2574_, v_sz_2573_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_bs_2575_);
return v___x_2582_;
}
else
{
lean_object* v_v_2583_; lean_object* v___x_2584_; lean_object* v_bs_x27_2585_; lean_object* v___x_2586_; 
v_v_2583_ = lean_array_uget(v_bs_2575_, v_i_2574_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v_bs_x27_2585_ = lean_array_uset(v_bs_2575_, v_i_2574_, v___x_2584_);
lean_inc(v___y_2579_);
lean_inc_ref(v___y_2578_);
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2576_);
v___x_2586_ = lean_infer_type(v_v_2583_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; size_t v___x_2588_; size_t v___x_2589_; lean_object* v___x_2590_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_add(v_i_2574_, v___x_2588_);
v___x_2590_ = lean_array_uset(v_bs_x27_2585_, v_i_2574_, v_a_2587_);
v_i_2574_ = v___x_2589_;
v_bs_2575_ = v___x_2590_;
goto _start;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_bs_x27_2585_);
v_a_2592_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2586_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2586_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2573_ = stack[0].m_num;
size_t v_i_2574_ = stack[1].m_num;
lean_object* v_bs_2575_ = stack[2].m_obj;
lean_object* v___y_2576_ = stack[3].m_obj;
lean_object* v___y_2577_ = stack[4].m_obj;
lean_object* v___y_2578_ = stack[5].m_obj;
lean_object* v___y_2579_ = stack[6].m_obj;
lean_object* v_res_2600_;
v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2573_, v_i_2574_, v_bs_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
stack->m_obj
 = v_res_2600_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(lean_object* v_sz_2601_, lean_object* v_i_2602_, lean_object* v_bs_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
size_t v_sz_boxed_2609_; size_t v_i_boxed_2610_; lean_object* v_res_2611_; 
v_sz_boxed_2609_ = lean_unbox_usize(v_sz_2601_);
lean_dec(v_sz_2601_);
v_i_boxed_2610_ = lean_unbox_usize(v_i_2602_);
lean_dec(v_i_2602_);
v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_boxed_2609_, v_i_boxed_2610_, v_bs_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2611_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry(lean_object* v_es_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
size_t v_sz_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v_sz_2618_ = lean_array_size(v_es_2612_);
v___x_2619_ = ((size_t)0ULL);
lean_inc_ref(v_es_2612_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2618_, v___x_2619_, v_es_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2622_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2621_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2624_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2624_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_a_2623_, v_es_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
return v___x_2624_;
}
else
{
lean_dec_ref(v_es_2612_);
return v___x_2622_;
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_es_2612_);
v_a_2625_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2620_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2620_);
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
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_uncurry_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_2612_ = stack[0].m_obj;
lean_object* v_a_2613_ = stack[1].m_obj;
lean_object* v_a_2614_ = stack[2].m_obj;
lean_object* v_a_2615_ = stack[3].m_obj;
lean_object* v_a_2616_ = stack[4].m_obj;
lean_object* v_res_2633_;
v_res_2633_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_es_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
stack->m_obj
 = v_res_2633_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(lean_object* v_es_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_es_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2640_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2642_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2643_ = lean_unsigned_to_nat(21u);
v___x_2644_ = lean_unsigned_to_nat(434u);
v___x_2645_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0));
v___x_2646_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2647_ = l_mkPanicMessageWithDecl(v___x_2646_, v___x_2645_, v___x_2644_, v___x_2643_, v___x_2642_);
return v___x_2647_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(lean_object* v___x_2648_, lean_object* v_es_2649_, lean_object* v_xs_2650_, lean_object* v_codomain_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = lean_array_get_size(v_xs_2650_);
v___x_2658_ = lean_nat_dec_eq(v___x_2657_, v___x_2648_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_dec_ref(v_codomain_2651_);
lean_dec_ref(v_es_2649_);
v___x_2659_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1);
v___x_2660_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2659_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
return v___x_2660_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = lean_unsigned_to_nat(0u);
v___x_2662_ = lean_array_fget_borrowed(v_xs_2650_, v___x_2661_);
v___x_2663_ = lean_array_to_list(v_es_2649_);
lean_inc(v___x_2662_);
v___x_2664_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2662_, v_codomain_2651_, v___x_2663_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; uint8_t v___x_2669_; lean_object* v___x_2670_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = lean_mk_empty_array_with_capacity(v___x_2648_);
lean_inc(v___x_2662_);
v___x_2667_ = lean_array_push(v___x_2666_, v___x_2662_);
v___x_2668_ = 0;
v___x_2669_ = 1;
v___x_2670_ = l_Lean_Meta_mkLambdaFVars(v___x_2667_, v_a_2665_, v___x_2668_, v___x_2658_, v___x_2668_, v___x_2658_, v___x_2669_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec_ref(v___x_2667_);
return v___x_2670_;
}
else
{
return v___x_2664_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2648_ = stack[0].m_obj;
lean_object* v_es_2649_ = stack[1].m_obj;
lean_object* v_xs_2650_ = stack[2].m_obj;
lean_object* v_codomain_2651_ = stack[3].m_obj;
lean_object* v___y_2652_ = stack[4].m_obj;
lean_object* v___y_2653_ = stack[5].m_obj;
lean_object* v___y_2654_ = stack[6].m_obj;
lean_object* v___y_2655_ = stack[7].m_obj;
lean_object* v_res_2671_;
v_res_2671_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2648_, v_es_2649_, v_xs_2650_, v_codomain_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
stack->m_obj
 = v_res_2671_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object* v___x_2672_, lean_object* v_es_2673_, lean_object* v_xs_2674_, lean_object* v_codomain_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2672_, v_es_2673_, v_xs_2674_, v_codomain_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec_ref(v_xs_2674_);
lean_dec(v___x_2672_);
return v_res_2681_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object* v_es_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
size_t v_sz_2688_; size_t v___x_2689_; lean_object* v___x_2690_; 
v_sz_2688_ = lean_array_size(v_es_2682_);
v___x_2689_ = ((size_t)0ULL);
lean_inc_ref(v_es_2682_);
v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2688_, v___x_2689_, v_es_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
v___x_2692_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_a_2691_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = lean_unsigned_to_nat(1u);
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2695_, 0, v___x_2694_);
lean_closure_set(v___f_2695_, 1, v_es_2682_);
v___x_2696_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2697_ = 0;
v___x_2698_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_2693_, v___x_2696_, v___f_2695_, v___x_2697_, v___x_2697_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
return v___x_2698_;
}
else
{
lean_dec_ref(v_es_2682_);
return v___x_2692_;
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec_ref(v_es_2682_);
v_a_2699_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2690_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2690_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_uncurryND_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_2682_ = stack[0].m_obj;
lean_object* v_a_2683_ = stack[1].m_obj;
lean_object* v_a_2684_ = stack[2].m_obj;
lean_object* v_a_2685_ = stack[3].m_obj;
lean_object* v_a_2686_ = stack[4].m_obj;
lean_object* v_res_2707_;
v_res_2707_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
stack->m_obj
 = v_res_2707_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object* v_es_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
return v_res_2714_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object* v_a_2715_, lean_object* v_domain_2716_, lean_object* v___x_2717_, lean_object* v_type_2718_, uint8_t v___x_2719_, lean_object* v_x_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = l_List_lengthTR___redArg(v_a_2715_);
lean_inc_ref(v_x_2720_);
v___x_2727_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2726_, v_domain_2716_, v___x_2717_, v_x_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___x_2726_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2729_ = lean_unsigned_to_nat(1u);
v___x_2730_ = lean_mk_empty_array_with_capacity(v___x_2729_);
lean_inc_ref(v___x_2730_);
v___x_2731_ = lean_array_push(v___x_2730_, v_a_2728_);
v___x_2732_ = l_Lean_Meta_instantiateForall(v_type_2718_, v___x_2731_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec_ref(v___x_2731_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; uint8_t v___x_2736_; lean_object* v___x_2737_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = lean_array_push(v___x_2730_, v_x_2720_);
v___x_2735_ = 0;
v___x_2736_ = 1;
v___x_2737_ = l_Lean_Meta_mkForallFVars(v___x_2734_, v_a_2733_, v___x_2735_, v___x_2719_, v___x_2719_, v___x_2736_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec_ref(v___x_2734_);
return v___x_2737_;
}
else
{
lean_dec_ref(v___x_2730_);
lean_dec_ref(v_x_2720_);
return v___x_2732_;
}
}
else
{
lean_dec_ref(v_x_2720_);
lean_dec_ref(v_type_2718_);
return v___x_2727_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2715_ = stack[0].m_obj;
lean_object* v_domain_2716_ = stack[1].m_obj;
lean_object* v___x_2717_ = stack[2].m_obj;
lean_object* v_type_2718_ = stack[3].m_obj;
uint8_t v___x_2719_ = stack[4].m_num;
lean_object* v_x_2720_ = stack[5].m_obj;
lean_object* v___y_2721_ = stack[6].m_obj;
lean_object* v___y_2722_ = stack[7].m_obj;
lean_object* v___y_2723_ = stack[8].m_obj;
lean_object* v___y_2724_ = stack[9].m_obj;
lean_object* v_res_2738_;
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2715_, v_domain_2716_, v___x_2717_, v_type_2718_, v___x_2719_, v_x_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
stack->m_obj
 = v_res_2738_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object* v_a_2739_, lean_object* v_domain_2740_, lean_object* v___x_2741_, lean_object* v_type_2742_, lean_object* v___x_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v___x_791__boxed_2750_; lean_object* v_res_2751_; 
v___x_791__boxed_2750_ = lean_unbox(v___x_2743_);
v_res_2751_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2739_, v_domain_2740_, v___x_2741_, v_type_2742_, v___x_791__boxed_2750_, v_x_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___x_2741_);
lean_dec(v_a_2739_);
return v_res_2751_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object* v_a_2752_, lean_object* v_domain_2753_, lean_object* v_type_2754_, size_t v_sz_2755_, size_t v_i_2756_, lean_object* v_bs_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_lt(v_i_2756_, v_sz_2755_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
lean_dec_ref(v_type_2754_);
lean_dec_ref(v_domain_2753_);
lean_dec(v_a_2752_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_bs_2757_);
return v___x_2764_;
}
else
{
lean_object* v_v_2765_; lean_object* v___x_2766_; lean_object* v_bs_x27_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_v_2765_ = lean_array_uget(v_bs_2757_, v_i_2756_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v_bs_x27_2767_ = lean_array_uset(v_bs_2757_, v_i_2756_, v___x_2766_);
v___x_2768_ = lean_usize_to_nat(v_i_2756_);
v___x_2769_ = lean_box(v___x_2763_);
lean_inc_ref(v_type_2754_);
lean_inc_ref(v_domain_2753_);
lean_inc(v_a_2752_);
v___f_2770_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2770_, 0, v_a_2752_);
lean_closure_set(v___f_2770_, 1, v_domain_2753_);
lean_closure_set(v___f_2770_, 2, v___x_2768_);
lean_closure_set(v___f_2770_, 3, v_type_2754_);
lean_closure_set(v___f_2770_, 4, v___x_2769_);
v___x_2771_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2772_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_2771_, v_v_2765_, v___f_2770_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; size_t v___x_2774_; size_t v___x_2775_; lean_object* v___x_2776_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v___x_2774_ = ((size_t)1ULL);
v___x_2775_ = lean_usize_add(v_i_2756_, v___x_2774_);
v___x_2776_ = lean_array_uset(v_bs_x27_2767_, v_i_2756_, v_a_2773_);
v_i_2756_ = v___x_2775_;
v_bs_2757_ = v___x_2776_;
goto _start;
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v_bs_x27_2767_);
lean_dec_ref(v_type_2754_);
lean_dec_ref(v_domain_2753_);
lean_dec(v_a_2752_);
v_a_2778_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2772_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2772_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2752_ = stack[0].m_obj;
lean_object* v_domain_2753_ = stack[1].m_obj;
lean_object* v_type_2754_ = stack[2].m_obj;
size_t v_sz_2755_ = stack[3].m_num;
size_t v_i_2756_ = stack[4].m_num;
lean_object* v_bs_2757_ = stack[5].m_obj;
lean_object* v___y_2758_ = stack[6].m_obj;
lean_object* v___y_2759_ = stack[7].m_obj;
lean_object* v___y_2760_ = stack[8].m_obj;
lean_object* v___y_2761_ = stack[9].m_obj;
lean_object* v_res_2786_;
v_res_2786_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2752_, v_domain_2753_, v_type_2754_, v_sz_2755_, v_i_2756_, v_bs_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
stack->m_obj
 = v_res_2786_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object* v_a_2787_, lean_object* v_domain_2788_, lean_object* v_type_2789_, lean_object* v_sz_2790_, lean_object* v_i_2791_, lean_object* v_bs_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
size_t v_sz_boxed_2798_; size_t v_i_boxed_2799_; lean_object* v_res_2800_; 
v_sz_boxed_2798_ = lean_unbox_usize(v_sz_2790_);
lean_dec(v_sz_2790_);
v_i_boxed_2799_ = lean_unbox_usize(v_i_2791_);
lean_dec(v_i_2791_);
v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2787_, v_domain_2788_, v_type_2789_, v_sz_boxed_2798_, v_i_boxed_2799_, v_bs_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
return v_res_2800_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object* v_n_2801_, lean_object* v_type_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; uint8_t v___x_2828_; 
v___x_2828_ = l_Lean_Expr_isForall(v_type_2802_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
v___x_2829_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_2830_ = l_Lean_MessageData_ofExpr(v_type_2802_);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2831_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
else
{
v___y_2809_ = v_a_2803_;
v___y_2810_ = v_a_2804_;
v___y_2811_ = v_a_2805_;
v___y_2812_ = v_a_2806_;
goto v___jp_2808_;
}
v___jp_2808_:
{
lean_object* v_domain_2813_; lean_object* v___x_2814_; 
v_domain_2813_ = l_Lean_Expr_bindingDomain_x21(v_type_2802_);
lean_inc_ref(v_domain_2813_);
v___x_2814_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_2801_, v_domain_2813_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; size_t v_sz_2817_; size_t v___x_2818_; lean_object* v___x_2819_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc_n(v_a_2815_, 2);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = lean_array_mk(v_a_2815_);
v_sz_2817_ = lean_array_size(v___x_2816_);
v___x_2818_ = ((size_t)0ULL);
v___x_2819_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2815_, v_domain_2813_, v_type_2802_, v_sz_2817_, v___x_2818_, v___x_2816_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v___x_2819_;
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_domain_2813_);
lean_dec_ref(v_type_2802_);
v_a_2820_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2814_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2814_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_Mutual_curryType_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2801_ = stack[0].m_obj;
lean_object* v_type_2802_ = stack[1].m_obj;
lean_object* v_a_2803_ = stack[2].m_obj;
lean_object* v_a_2804_ = stack[3].m_obj;
lean_object* v_a_2805_ = stack[4].m_obj;
lean_object* v_a_2806_ = stack[5].m_obj;
lean_object* v_res_2841_;
v_res_2841_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2801_, v_type_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
stack->m_obj
 = v_res_2841_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object* v_n_2842_, lean_object* v_type_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2842_, v_type_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_n_2842_);
return v_res_2849_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object* v_a_2850_, lean_object* v_domain_2851_, lean_object* v_type_2852_, lean_object* v_as_2853_, size_t v_sz_2854_, size_t v_i_2855_, lean_object* v_bs_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2850_, v_domain_2851_, v_type_2852_, v_sz_2854_, v_i_2855_, v_bs_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2850_ = stack[0].m_obj;
lean_object* v_domain_2851_ = stack[1].m_obj;
lean_object* v_type_2852_ = stack[2].m_obj;
lean_object* v_as_2853_ = stack[3].m_obj;
size_t v_sz_2854_ = stack[4].m_num;
size_t v_i_2855_ = stack[5].m_num;
lean_object* v_bs_2856_ = stack[6].m_obj;
lean_object* v___y_2857_ = stack[7].m_obj;
lean_object* v___y_2858_ = stack[8].m_obj;
lean_object* v___y_2859_ = stack[9].m_obj;
lean_object* v___y_2860_ = stack[10].m_obj;
lean_object* v_res_2863_;
v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2850_, v_domain_2851_, v_type_2852_, v_as_2853_, v_sz_2854_, v_i_2855_, v_bs_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
stack->m_obj
 = v_res_2863_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object* v_a_2864_, lean_object* v_domain_2865_, lean_object* v_type_2866_, lean_object* v_as_2867_, lean_object* v_sz_2868_, lean_object* v_i_2869_, lean_object* v_bs_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2868_);
lean_dec(v_sz_2868_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2864_, v_domain_2865_, v_type_2866_, v_as_2867_, v_sz_boxed_2876_, v_i_boxed_2877_, v_bs_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_as_2867_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object* v_argsPacker_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_array_get_size(v_argsPacker_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object* v_argsPacker_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_2881_);
lean_dec_ref(v_argsPacker_2881_);
return v_res_2882_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t v_sz_2883_, size_t v_i_2884_, lean_object* v_bs_2885_){
_start:
{
uint8_t v___x_2886_; 
v___x_2886_ = lean_usize_dec_lt(v_i_2884_, v_sz_2883_);
if (v___x_2886_ == 0)
{
return v_bs_2885_;
}
else
{
lean_object* v_v_2887_; lean_object* v___x_2888_; lean_object* v_bs_x27_2889_; lean_object* v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; lean_object* v___x_2893_; 
v_v_2887_ = lean_array_uget(v_bs_2885_, v_i_2884_);
v___x_2888_ = lean_unsigned_to_nat(0u);
v_bs_x27_2889_ = lean_array_uset(v_bs_2885_, v_i_2884_, v___x_2888_);
v___x_2890_ = lean_array_get_size(v_v_2887_);
lean_dec(v_v_2887_);
v___x_2891_ = ((size_t)1ULL);
v___x_2892_ = lean_usize_add(v_i_2884_, v___x_2891_);
v___x_2893_ = lean_array_uset(v_bs_x27_2889_, v_i_2884_, v___x_2890_);
v_i_2884_ = v___x_2892_;
v_bs_2885_ = v___x_2893_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2883_ = stack[0].m_num;
size_t v_i_2884_ = stack[1].m_num;
lean_object* v_bs_2885_ = stack[2].m_obj;
lean_object* v_res_2895_;
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2883_, v_i_2884_, v_bs_2885_);
stack->m_obj
 = v_res_2895_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object* v_sz_2896_, lean_object* v_i_2897_, lean_object* v_bs_2898_){
_start:
{
size_t v_sz_boxed_2899_; size_t v_i_boxed_2900_; lean_object* v_res_2901_; 
v_sz_boxed_2899_ = lean_unbox_usize(v_sz_2896_);
lean_dec(v_sz_2896_);
v_i_boxed_2900_ = lean_unbox_usize(v_i_2897_);
lean_dec(v_i_2897_);
v_res_2901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_2899_, v_i_boxed_2900_, v_bs_2898_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object* v_argsPacker_2902_){
_start:
{
size_t v_sz_2903_; size_t v___x_2904_; lean_object* v___x_2905_; 
v_sz_2903_ = lean_array_size(v_argsPacker_2902_);
v___x_2904_ = ((size_t)0ULL);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2903_, v___x_2904_, v_argsPacker_2902_);
return v___x_2905_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0(void){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Array_instInhabited___redArg();
return v___x_2906_;
}
}
uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object* v_argsPacker_2907_){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2908_ = lean_array_get_size(v_argsPacker_2907_);
v___x_2909_ = lean_unsigned_to_nat(1u);
v___x_2910_ = lean_nat_dec_eq(v___x_2908_, v___x_2909_);
if (v___x_2910_ == 0)
{
return v___x_2910_;
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2911_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2912_ = lean_unsigned_to_nat(0u);
v___x_2913_ = lean_array_get_borrowed(v___x_2911_, v_argsPacker_2907_, v___x_2912_);
v___x_2914_ = lean_array_get_size(v___x_2913_);
v___x_2915_ = lean_nat_dec_eq(v___x_2914_, v___x_2909_);
return v___x_2915_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_onlyOneUnary_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_2907_ = stack[0].m_obj;
uint8_t v_res_2916_;
v_res_2916_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2907_);
stack->m_num = v_res_2916_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object* v_argsPacker_2917_){
_start:
{
uint8_t v_res_2918_; lean_object* v_r_2919_; 
v_res_2918_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2917_);
lean_dec_ref(v_argsPacker_2917_);
v_r_2919_ = lean_box(v_res_2918_);
return v_r_2919_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__2(void){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2922_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__1));
v___x_2923_ = lean_unsigned_to_nat(2u);
v___x_2924_ = lean_unsigned_to_nat(469u);
v___x_2925_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2926_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2927_ = l_mkPanicMessageWithDecl(v___x_2926_, v___x_2925_, v___x_2924_, v___x_2923_, v___x_2922_);
return v___x_2927_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__4(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2929_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__3));
v___x_2930_ = lean_unsigned_to_nat(2u);
v___x_2931_ = lean_unsigned_to_nat(470u);
v___x_2932_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2933_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2934_ = l_mkPanicMessageWithDecl(v___x_2933_, v___x_2932_, v___x_2931_, v___x_2930_, v___x_2929_);
return v___x_2934_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object* v_argsPacker_2935_, lean_object* v_domain_2936_, lean_object* v_fidx_2937_, lean_object* v_args_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_array_get_size(v_argsPacker_2935_);
v___x_2945_ = lean_nat_dec_lt(v_fidx_2937_, v___x_2944_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
lean_dec(v_fidx_2937_);
lean_dec_ref(v_domain_2936_);
v___x_2946_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__2, &l_Lean_Meta_ArgsPacker_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__2);
v___x_2947_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2946_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
return v___x_2947_;
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2948_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2949_ = lean_array_get_size(v_args_2938_);
v___x_2950_ = lean_array_get_borrowed(v___x_2948_, v_argsPacker_2935_, v_fidx_2937_);
v___x_2951_ = lean_array_get_size(v___x_2950_);
v___x_2952_ = lean_nat_dec_eq(v___x_2949_, v___x_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec(v_fidx_2937_);
lean_dec_ref(v_domain_2936_);
v___x_2953_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__4, &l_Lean_Meta_ArgsPacker_pack___closed__4_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__4);
v___x_2954_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2953_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_domain_2936_);
v___x_2956_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_2944_, v_domain_2936_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
lean_inc(v_fidx_2937_);
v___x_2958_ = l_List_get_x21Internal___redArg(v___x_2955_, v_a_2957_, v_fidx_2937_);
lean_dec(v_a_2957_);
v___x_2959_ = l_Lean_Meta_ArgsPacker_Unary_pack(v___x_2958_, v_args_2938_);
lean_dec(v___x_2958_);
v___x_2960_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2944_, v_domain_2936_, v_fidx_2937_, v___x_2959_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_fidx_2937_);
return v___x_2960_;
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_fidx_2937_);
lean_dec_ref(v_domain_2936_);
v_a_2961_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2956_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2956_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_pack_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_2935_ = stack[0].m_obj;
lean_object* v_domain_2936_ = stack[1].m_obj;
lean_object* v_fidx_2937_ = stack[2].m_obj;
lean_object* v_args_2938_ = stack[3].m_obj;
lean_object* v_a_2939_ = stack[4].m_obj;
lean_object* v_a_2940_ = stack[5].m_obj;
lean_object* v_a_2941_ = stack[6].m_obj;
lean_object* v_a_2942_ = stack[7].m_obj;
lean_object* v_res_2969_;
v_res_2969_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2935_, v_domain_2936_, v_fidx_2937_, v_args_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
stack->m_obj
 = v_res_2969_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object* v_argsPacker_2970_, lean_object* v_domain_2971_, lean_object* v_fidx_2972_, lean_object* v_args_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2970_, v_domain_2971_, v_fidx_2972_, v_args_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec_ref(v_args_2973_);
lean_dec_ref(v_argsPacker_2970_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object* v_argsPacker_2980_, lean_object* v_e_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_array_get_size(v_argsPacker_2980_);
v___x_2983_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_2982_, v_e_2981_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_box(0);
return v___x_2984_;
}
else
{
lean_object* v_val_2985_; lean_object* v_fst_2986_; lean_object* v_snd_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3007_; 
v_val_2985_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_val_2985_);
lean_dec_ref_known(v___x_2983_, 1);
v_fst_2986_ = lean_ctor_get(v_val_2985_, 0);
v_snd_2987_ = lean_ctor_get(v_val_2985_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_val_2985_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2989_ = v_val_2985_;
v_isShared_2990_ = v_isSharedCheck_3007_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_snd_2987_);
lean_inc(v_fst_2986_);
lean_dec(v_val_2985_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3007_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2991_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2992_ = lean_array_get_borrowed(v___x_2991_, v_argsPacker_2980_, v_fst_2986_);
v___x_2993_ = lean_array_get_size(v___x_2992_);
v___x_2994_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_2993_, v_snd_2987_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v___x_2995_; 
lean_del_object(v___x_2989_);
lean_dec(v_fst_2986_);
v___x_2995_ = lean_box(0);
return v___x_2995_;
}
else
{
lean_object* v_val_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3006_; 
v_val_2996_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2998_ = v___x_2994_;
v_isShared_2999_ = v_isSharedCheck_3006_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_val_2996_);
lean_dec(v___x_2994_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3006_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v_val_2996_);
v___x_3001_ = v___x_2989_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_fst_2986_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_val_2996_);
v___x_3001_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3003_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3001_);
v___x_3003_ = v___x_2998_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object* v_argsPacker_3008_, lean_object* v_e_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_3008_, v_e_3009_);
lean_dec_ref(v_argsPacker_3008_);
return v_res_3010_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object* v_as_3011_, lean_object* v_bs_3012_, lean_object* v_i_3013_, lean_object* v_cs_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = lean_array_get_size(v_as_3011_);
v___x_3021_ = lean_nat_dec_lt(v_i_3013_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
lean_dec(v_i_3013_);
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v_cs_3014_);
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = lean_array_get_size(v_bs_3012_);
v___x_3024_ = lean_nat_dec_lt(v_i_3013_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; 
lean_dec(v_i_3013_);
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_cs_3014_);
return v___x_3025_;
}
else
{
lean_object* v_a_3026_; lean_object* v_b_3027_; lean_object* v___x_3028_; 
v_a_3026_ = lean_array_fget_borrowed(v_as_3011_, v_i_3013_);
v_b_3027_ = lean_array_fget_borrowed(v_bs_3012_, v_i_3013_);
lean_inc(v_b_3027_);
lean_inc(v_a_3026_);
v___x_3028_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_a_3026_, v_b_3027_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3030_ = lean_unsigned_to_nat(1u);
v___x_3031_ = lean_nat_add(v_i_3013_, v___x_3030_);
lean_dec(v_i_3013_);
v___x_3032_ = lean_array_push(v_cs_3014_, v_a_3029_);
v_i_3013_ = v___x_3031_;
v_cs_3014_ = v___x_3032_;
goto _start;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v_cs_3014_);
lean_dec(v_i_3013_);
v_a_3034_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3028_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3028_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3011_ = stack[0].m_obj;
lean_object* v_bs_3012_ = stack[1].m_obj;
lean_object* v_i_3013_ = stack[2].m_obj;
lean_object* v_cs_3014_ = stack[3].m_obj;
lean_object* v___y_3015_ = stack[4].m_obj;
lean_object* v___y_3016_ = stack[5].m_obj;
lean_object* v___y_3017_ = stack[6].m_obj;
lean_object* v___y_3018_ = stack[7].m_obj;
lean_object* v_res_3042_;
v_res_3042_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_3011_, v_bs_3012_, v_i_3013_, v_cs_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
stack->m_obj
 = v_res_3042_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object* v_as_3043_, lean_object* v_bs_3044_, lean_object* v_i_3045_, lean_object* v_cs_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_3043_, v_bs_3044_, v_i_3045_, v_cs_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec_ref(v_bs_3044_);
lean_dec_ref(v_as_3043_);
return v_res_3052_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object* v_argsPacker_3053_, lean_object* v_types_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_unsigned_to_nat(0u);
v___x_3061_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3062_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_argsPacker_3053_, v_types_3054_, v___x_3060_, v___x_3061_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___x_3064_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_3063_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
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
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_uncurryType_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3053_ = stack[0].m_obj;
lean_object* v_types_3054_ = stack[1].m_obj;
lean_object* v_a_3055_ = stack[2].m_obj;
lean_object* v_a_3056_ = stack[3].m_obj;
lean_object* v_a_3057_ = stack[4].m_obj;
lean_object* v_a_3058_ = stack[5].m_obj;
lean_object* v_res_3073_;
v_res_3073_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_3053_, v_types_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
stack->m_obj
 = v_res_3073_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object* v_argsPacker_3074_, lean_object* v_types_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_3074_, v_types_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec_ref(v_types_3075_);
lean_dec_ref(v_argsPacker_3074_);
return v_res_3081_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object* v_as_3082_, lean_object* v_bs_3083_, lean_object* v_i_3084_, lean_object* v_cs_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3091_ = lean_array_get_size(v_as_3082_);
v___x_3092_ = lean_nat_dec_lt(v_i_3084_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; 
lean_dec(v_i_3084_);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v_cs_3085_);
return v___x_3093_;
}
else
{
lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = lean_array_get_size(v_bs_3083_);
v___x_3095_ = lean_nat_dec_lt(v_i_3084_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; 
lean_dec(v_i_3084_);
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v_cs_3085_);
return v___x_3096_;
}
else
{
lean_object* v_a_3097_; lean_object* v_b_3098_; lean_object* v___x_3099_; 
v_a_3097_ = lean_array_fget_borrowed(v_as_3082_, v_i_3084_);
v_b_3098_ = lean_array_fget_borrowed(v_bs_3083_, v_i_3084_);
lean_inc(v_b_3098_);
lean_inc(v_a_3097_);
v___x_3099_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_a_3097_, v_b_3098_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3099_, 1);
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_add(v_i_3084_, v___x_3101_);
lean_dec(v_i_3084_);
v___x_3103_ = lean_array_push(v_cs_3085_, v_a_3100_);
v_i_3084_ = v___x_3102_;
v_cs_3085_ = v___x_3103_;
goto _start;
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref(v_cs_3085_);
lean_dec(v_i_3084_);
v_a_3105_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3099_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3099_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3082_ = stack[0].m_obj;
lean_object* v_bs_3083_ = stack[1].m_obj;
lean_object* v_i_3084_ = stack[2].m_obj;
lean_object* v_cs_3085_ = stack[3].m_obj;
lean_object* v___y_3086_ = stack[4].m_obj;
lean_object* v___y_3087_ = stack[5].m_obj;
lean_object* v___y_3088_ = stack[6].m_obj;
lean_object* v___y_3089_ = stack[7].m_obj;
lean_object* v_res_3113_;
v_res_3113_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3082_, v_bs_3083_, v_i_3084_, v_cs_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
stack->m_obj
 = v_res_3113_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object* v_as_3114_, lean_object* v_bs_3115_, lean_object* v_i_3116_, lean_object* v_cs_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3114_, v_bs_3115_, v_i_3116_, v_cs_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v_bs_3115_);
lean_dec_ref(v_as_3114_);
return v_res_3123_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object* v_argsPacker_3124_, lean_object* v_es_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3133_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3124_, v_es_3125_, v___x_3131_, v___x_3132_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3135_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3133_, 1);
v___x_3135_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_a_3134_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
return v___x_3135_;
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3133_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3133_);
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
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_uncurry_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3124_ = stack[0].m_obj;
lean_object* v_es_3125_ = stack[1].m_obj;
lean_object* v_a_3126_ = stack[2].m_obj;
lean_object* v_a_3127_ = stack[3].m_obj;
lean_object* v_a_3128_ = stack[4].m_obj;
lean_object* v_a_3129_ = stack[5].m_obj;
lean_object* v_res_3144_;
v_res_3144_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3124_, v_es_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
stack->m_obj
 = v_res_3144_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object* v_argsPacker_3145_, lean_object* v_es_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3145_, v_es_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec_ref(v_es_3146_);
lean_dec_ref(v_argsPacker_3145_);
return v_res_3152_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object* v_argsPacker_3153_, lean_object* v_resultType_3154_, lean_object* v_es_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3163_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3153_, v_es_3155_, v___x_3161_, v___x_3162_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_3154_, v_a_3164_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
return v___x_3165_;
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref(v_resultType_3154_);
v_a_3166_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3163_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3163_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_uncurryWithType_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3153_ = stack[0].m_obj;
lean_object* v_resultType_3154_ = stack[1].m_obj;
lean_object* v_es_3155_ = stack[2].m_obj;
lean_object* v_a_3156_ = stack[3].m_obj;
lean_object* v_a_3157_ = stack[4].m_obj;
lean_object* v_a_3158_ = stack[5].m_obj;
lean_object* v_a_3159_ = stack[6].m_obj;
lean_object* v_res_3174_;
v_res_3174_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3153_, v_resultType_3154_, v_es_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
stack->m_obj
 = v_res_3174_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object* v_argsPacker_3175_, lean_object* v_resultType_3176_, lean_object* v_es_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3175_, v_resultType_3176_, v_es_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v_es_3177_);
lean_dec_ref(v_argsPacker_3175_);
return v_res_3183_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object* v_argsPacker_3184_, lean_object* v_es_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3193_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3184_, v_es_3185_, v___x_3191_, v___x_3192_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3195_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v___x_3193_, 1);
v___x_3195_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_a_3194_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
return v___x_3195_;
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3193_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3193_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_uncurryND_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3184_ = stack[0].m_obj;
lean_object* v_es_3185_ = stack[1].m_obj;
lean_object* v_a_3186_ = stack[2].m_obj;
lean_object* v_a_3187_ = stack[3].m_obj;
lean_object* v_a_3188_ = stack[4].m_obj;
lean_object* v_a_3189_ = stack[5].m_obj;
lean_object* v_res_3204_;
v_res_3204_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3184_, v_es_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
stack->m_obj
 = v_res_3204_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object* v_argsPacker_3205_, lean_object* v_es_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3205_, v_es_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec_ref(v_es_3206_);
lean_dec_ref(v_argsPacker_3205_);
return v_res_3212_;
}
}
lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object* v_msg_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___f_3219_; lean_object* v___x_920__overap_3220_; lean_object* v___x_3221_; 
v___f_3219_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_920__overap_3220_ = lean_panic_fn_borrowed(v___f_3219_, v_msg_3213_);
lean_inc(v___y_3217_);
lean_inc_ref(v___y_3216_);
lean_inc(v___y_3215_);
lean_inc_ref(v___y_3214_);
v___x_3221_ = lean_apply_5(v___x_920__overap_3220_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, lean_box(0));
return v___x_3221_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3213_ = stack[0].m_obj;
lean_object* v___y_3214_ = stack[1].m_obj;
lean_object* v___y_3215_ = stack[2].m_obj;
lean_object* v___y_3216_ = stack[3].m_obj;
lean_object* v___y_3217_ = stack[4].m_obj;
lean_object* v_res_3222_;
v_res_3222_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
stack->m_obj
 = v_res_3222_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object* v_msg_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3229_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object* v_a_3230_, lean_object* v___x_3231_, lean_object* v_i_3232_, lean_object* v_e_3233_, lean_object* v_x_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = l_List_lengthTR___redArg(v_a_3230_);
lean_inc_ref(v_x_3234_);
v___x_3241_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_3240_, v___x_3231_, v_i_3232_, v_x_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___x_3240_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; uint8_t v___x_3249_; uint8_t v___x_3250_; lean_object* v___x_3251_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v___x_3243_ = lean_unsigned_to_nat(1u);
v___x_3244_ = lean_mk_empty_array_with_capacity(v___x_3243_);
lean_inc_ref(v___x_3244_);
v___x_3245_ = lean_array_push(v___x_3244_, v_x_3234_);
v___x_3246_ = lean_array_push(v___x_3244_, v_a_3242_);
v___x_3247_ = l_Lean_Expr_beta(v_e_3233_, v___x_3246_);
v___x_3248_ = 0;
v___x_3249_ = 1;
v___x_3250_ = 1;
v___x_3251_ = l_Lean_Meta_mkLambdaFVars(v___x_3245_, v___x_3247_, v___x_3248_, v___x_3249_, v___x_3248_, v___x_3249_, v___x_3250_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec_ref(v___x_3245_);
return v___x_3251_;
}
else
{
lean_dec_ref(v_x_3234_);
lean_dec_ref(v_e_3233_);
return v___x_3241_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_curryProj___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3230_ = stack[0].m_obj;
lean_object* v___x_3231_ = stack[1].m_obj;
lean_object* v_i_3232_ = stack[2].m_obj;
lean_object* v_e_3233_ = stack[3].m_obj;
lean_object* v_x_3234_ = stack[4].m_obj;
lean_object* v___y_3235_ = stack[5].m_obj;
lean_object* v___y_3236_ = stack[6].m_obj;
lean_object* v___y_3237_ = stack[7].m_obj;
lean_object* v___y_3238_ = stack[8].m_obj;
lean_object* v_res_3252_;
v_res_3252_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3230_, v___x_3231_, v_i_3232_, v_e_3233_, v_x_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
stack->m_obj
 = v_res_3252_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object* v_a_3253_, lean_object* v___x_3254_, lean_object* v_i_3255_, lean_object* v_e_3256_, lean_object* v_x_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3253_, v___x_3254_, v_i_3255_, v_e_3256_, v_x_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v_i_3255_);
lean_dec(v_a_3253_);
return v_res_3263_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__0));
v___x_3266_ = l_Lean_stringToMessageData(v___x_3265_);
return v___x_3266_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3269_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__3));
v___x_3270_ = lean_unsigned_to_nat(4u);
v___x_3271_ = lean_unsigned_to_nat(535u);
v___x_3272_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__2));
v___x_3273_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_3274_ = l_mkPanicMessageWithDecl(v___x_3273_, v___x_3272_, v___x_3271_, v___x_3270_, v___x_3269_);
return v___x_3274_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object* v_argsPacker_3275_, lean_object* v_e_3276_, lean_object* v_i_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v_n_3285_; lean_object* v___x_3286_; 
v___x_3283_ = l_Lean_instInhabitedExpr;
v___x_3284_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v_n_3285_ = lean_array_get_size(v_argsPacker_3275_);
lean_inc(v_a_3281_);
lean_inc_ref(v_a_3280_);
lean_inc(v_a_3279_);
lean_inc_ref(v_a_3278_);
lean_inc_ref(v_e_3276_);
v___x_3286_ = lean_infer_type(v_e_3276_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
lean_inc(v_a_3281_);
lean_inc_ref(v_a_3280_);
lean_inc(v_a_3279_);
lean_inc_ref(v_a_3278_);
v___x_3288_ = lean_whnf(v_a_3287_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; uint8_t v___x_3332_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3288_, 1);
v___x_3332_ = l_Lean_Expr_isForall(v_a_3289_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__4, &l_Lean_Meta_ArgsPacker_curryProj___closed__4_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4);
v___x_3334_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v___x_3333_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_dec_ref_known(v___x_3334_, 1);
v___y_3304_ = v_a_3278_;
v___y_3305_ = v_a_3279_;
v___y_3306_ = v_a_3280_;
v___y_3307_ = v_a_3281_;
goto v___jp_3303_;
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_a_3289_);
lean_dec(v_i_3277_);
lean_dec_ref(v_e_3276_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
v___y_3304_ = v_a_3278_;
v___y_3305_ = v_a_3279_;
v___y_3306_ = v_a_3280_;
v___y_3307_ = v_a_3281_;
goto v___jp_3303_;
}
v___jp_3290_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_inc(v_i_3277_);
v___x_3297_ = l_List_get_x21Internal___redArg(v___x_3283_, v___y_3291_, v_i_3277_);
lean_dec(v___y_3291_);
v___x_3298_ = l_Lean_Expr_bindingName_x21(v_a_3289_);
lean_dec(v_a_3289_);
v___x_3299_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3298_, v___x_3297_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = lean_array_get_borrowed(v___x_3284_, v_argsPacker_3275_, v_i_3277_);
lean_dec(v_i_3277_);
lean_inc(v___x_3301_);
v___x_3302_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v___x_3301_, v_a_3300_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
return v___x_3302_;
}
else
{
lean_dec(v_i_3277_);
return v___x_3299_;
}
}
v___jp_3303_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = l_Lean_Expr_bindingDomain_x21(v_a_3289_);
lean_inc_ref(v___x_3308_);
v___x_3309_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_3285_, v___x_3308_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc_n(v_a_3310_, 2);
lean_dec_ref_known(v___x_3309_, 1);
lean_inc(v_i_3277_);
v___f_3311_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3311_, 0, v_a_3310_);
lean_closure_set(v___f_3311_, 1, v___x_3308_);
lean_closure_set(v___f_3311_, 2, v_i_3277_);
lean_closure_set(v___f_3311_, 3, v_e_3276_);
v___x_3312_ = l_List_lengthTR___redArg(v_a_3310_);
v___x_3313_ = lean_nat_dec_lt(v_i_3277_, v___x_3312_);
lean_dec(v___x_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_dec_ref(v___f_3311_);
lean_dec(v_a_3310_);
lean_dec(v_a_3289_);
lean_dec(v_i_3277_);
v___x_3314_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__1, &l_Lean_Meta_ArgsPacker_curryProj___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1);
v___x_3315_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3314_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
else
{
v___y_3291_ = v_a_3310_;
v___y_3292_ = v___f_3311_;
v___y_3293_ = v___y_3304_;
v___y_3294_ = v___y_3305_;
v___y_3295_ = v___y_3306_;
v___y_3296_ = v___y_3307_;
goto v___jp_3290_;
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec_ref(v___x_3308_);
lean_dec(v_a_3289_);
lean_dec(v_i_3277_);
lean_dec_ref(v_e_3276_);
v_a_3324_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3309_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3309_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
else
{
lean_dec(v_i_3277_);
lean_dec_ref(v_e_3276_);
return v___x_3288_;
}
}
else
{
lean_dec(v_i_3277_);
lean_dec_ref(v_e_3276_);
return v___x_3286_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_curryProj_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3275_ = stack[0].m_obj;
lean_object* v_e_3276_ = stack[1].m_obj;
lean_object* v_i_3277_ = stack[2].m_obj;
lean_object* v_a_3278_ = stack[3].m_obj;
lean_object* v_a_3279_ = stack[4].m_obj;
lean_object* v_a_3280_ = stack[5].m_obj;
lean_object* v_a_3281_ = stack[6].m_obj;
lean_object* v_res_3343_;
v_res_3343_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3275_, v_e_3276_, v_i_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_);
stack->m_obj
 = v_res_3343_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object* v_argsPacker_3344_, lean_object* v_e_3345_, lean_object* v_i_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3344_, v_e_3345_, v_i_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec_ref(v_argsPacker_3344_);
return v_res_3352_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object* v_as_3353_, lean_object* v_bs_3354_, lean_object* v_i_3355_, lean_object* v_cs_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3362_; uint8_t v___x_3363_; 
v___x_3362_ = lean_array_get_size(v_as_3353_);
v___x_3363_ = lean_nat_dec_lt(v_i_3355_, v___x_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec(v_i_3355_);
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_cs_3356_);
return v___x_3364_;
}
else
{
lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_3365_ = lean_array_get_size(v_bs_3354_);
v___x_3366_ = lean_nat_dec_lt(v_i_3355_, v___x_3365_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; 
lean_dec(v_i_3355_);
v___x_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3367_, 0, v_cs_3356_);
return v___x_3367_;
}
else
{
lean_object* v_a_3368_; lean_object* v_b_3369_; lean_object* v___x_3370_; 
v_a_3368_ = lean_array_fget_borrowed(v_as_3353_, v_i_3355_);
v_b_3369_ = lean_array_fget_borrowed(v_bs_3354_, v_i_3355_);
lean_inc(v_b_3369_);
lean_inc(v_a_3368_);
v___x_3370_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_3368_, v_b_3369_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v___x_3372_ = lean_unsigned_to_nat(1u);
v___x_3373_ = lean_nat_add(v_i_3355_, v___x_3372_);
lean_dec(v_i_3355_);
v___x_3374_ = lean_array_push(v_cs_3356_, v_a_3371_);
v_i_3355_ = v___x_3373_;
v_cs_3356_ = v___x_3374_;
goto _start;
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref(v_cs_3356_);
lean_dec(v_i_3355_);
v_a_3376_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3370_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3370_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3353_ = stack[0].m_obj;
lean_object* v_bs_3354_ = stack[1].m_obj;
lean_object* v_i_3355_ = stack[2].m_obj;
lean_object* v_cs_3356_ = stack[3].m_obj;
lean_object* v___y_3357_ = stack[4].m_obj;
lean_object* v___y_3358_ = stack[5].m_obj;
lean_object* v___y_3359_ = stack[6].m_obj;
lean_object* v___y_3360_ = stack[7].m_obj;
lean_object* v_res_3384_;
v_res_3384_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3353_, v_bs_3354_, v_i_3355_, v_cs_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
stack->m_obj
 = v_res_3384_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object* v_as_3385_, lean_object* v_bs_3386_, lean_object* v_i_3387_, lean_object* v_cs_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3385_, v_bs_3386_, v_i_3387_, v_cs_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v_bs_3386_);
lean_dec_ref(v_as_3385_);
return v_res_3394_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object* v_argsPacker_3395_, lean_object* v_t_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_array_get_size(v_argsPacker_3395_);
v___x_3403_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v___x_3402_, v_t_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3403_, 1);
v___x_3405_ = lean_unsigned_to_nat(0u);
v___x_3406_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3407_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_argsPacker_3395_, v_a_3404_, v___x_3405_, v___x_3406_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
lean_dec(v_a_3404_);
return v___x_3407_;
}
else
{
return v___x_3403_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_curryType_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3395_ = stack[0].m_obj;
lean_object* v_t_3396_ = stack[1].m_obj;
lean_object* v_a_3397_ = stack[2].m_obj;
lean_object* v_a_3398_ = stack[3].m_obj;
lean_object* v_a_3399_ = stack[4].m_obj;
lean_object* v_a_3400_ = stack[5].m_obj;
lean_object* v_res_3408_;
v_res_3408_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3395_, v_t_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
stack->m_obj
 = v_res_3408_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object* v_argsPacker_3409_, lean_object* v_t_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3409_, v_t_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec_ref(v_argsPacker_3409_);
return v_res_3416_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object* v_upperBound_3417_, lean_object* v_argsPacker_3418_, lean_object* v_e_3419_, lean_object* v_a_3420_, lean_object* v_b_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_nat_dec_lt(v_a_3420_, v_upperBound_3417_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
lean_dec(v_a_3420_);
lean_dec_ref(v_e_3419_);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v_b_3421_);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; 
lean_inc(v_a_3420_);
lean_inc_ref(v_e_3419_);
v___x_3429_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3418_, v_e_3419_, v_a_3420_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v___x_3431_ = lean_array_push(v_b_3421_, v_a_3430_);
v___x_3432_ = lean_unsigned_to_nat(1u);
v___x_3433_ = lean_nat_add(v_a_3420_, v___x_3432_);
lean_dec(v_a_3420_);
v_a_3420_ = v___x_3433_;
v_b_3421_ = v___x_3431_;
goto _start;
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v_b_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_e_3419_);
v_a_3435_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3429_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3429_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3417_ = stack[0].m_obj;
lean_object* v_argsPacker_3418_ = stack[1].m_obj;
lean_object* v_e_3419_ = stack[2].m_obj;
lean_object* v_a_3420_ = stack[3].m_obj;
lean_object* v_b_3421_ = stack[4].m_obj;
lean_object* v___y_3422_ = stack[5].m_obj;
lean_object* v___y_3423_ = stack[6].m_obj;
lean_object* v___y_3424_ = stack[7].m_obj;
lean_object* v___y_3425_ = stack[8].m_obj;
lean_object* v_res_3443_;
v_res_3443_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3417_, v_argsPacker_3418_, v_e_3419_, v_a_3420_, v_b_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
stack->m_obj
 = v_res_3443_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object* v_upperBound_3444_, lean_object* v_argsPacker_3445_, lean_object* v_e_3446_, lean_object* v_a_3447_, lean_object* v_b_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3444_, v_argsPacker_3445_, v_e_3446_, v_a_3447_, v_b_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec_ref(v_argsPacker_3445_);
lean_dec(v_upperBound_3444_);
return v_res_3454_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curry___closed__0(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_unsigned_to_nat(0u);
v___x_3456_ = l_Lean_Level_ofNat(v___x_3455_);
return v___x_3456_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object* v_argsPacker_3457_, lean_object* v_e_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v_es_3466_; lean_object* v___x_3467_; 
v___x_3464_ = lean_array_get_size(v_argsPacker_3457_);
v___x_3465_ = lean_unsigned_to_nat(0u);
v_es_3466_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3467_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_3464_, v_argsPacker_3457_, v_e_3458_, v___x_3465_, v_es_3466_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curry___closed__0, &l_Lean_Meta_ArgsPacker_curry___closed__0_once, _init_l_Lean_Meta_ArgsPacker_curry___closed__0);
v___x_3470_ = l_Lean_Meta_PProdN_mk(v___x_3469_, v_a_3468_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
return v___x_3470_;
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
v_a_3471_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3467_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3467_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_curry_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3457_ = stack[0].m_obj;
lean_object* v_e_3458_ = stack[1].m_obj;
lean_object* v_a_3459_ = stack[2].m_obj;
lean_object* v_a_3460_ = stack[3].m_obj;
lean_object* v_a_3461_ = stack[4].m_obj;
lean_object* v_a_3462_ = stack[5].m_obj;
lean_object* v_res_3479_;
v_res_3479_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3457_, v_e_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
stack->m_obj
 = v_res_3479_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object* v_argsPacker_3480_, lean_object* v_e_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3480_, v_e_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec_ref(v_argsPacker_3480_);
return v_res_3487_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object* v_upperBound_3488_, lean_object* v_argsPacker_3489_, lean_object* v_e_3490_, lean_object* v_inst_3491_, lean_object* v_R_3492_, lean_object* v_a_3493_, lean_object* v_b_3494_, lean_object* v_c_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3488_, v_argsPacker_3489_, v_e_3490_, v_a_3493_, v_b_3494_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3488_ = stack[0].m_obj;
lean_object* v_argsPacker_3489_ = stack[1].m_obj;
lean_object* v_e_3490_ = stack[2].m_obj;
lean_object* v_a_3493_ = stack[5].m_obj;
lean_object* v_b_3494_ = stack[6].m_obj;
lean_object* v___y_3496_ = stack[8].m_obj;
lean_object* v___y_3497_ = stack[9].m_obj;
lean_object* v___y_3498_ = stack[10].m_obj;
lean_object* v___y_3499_ = stack[11].m_obj;
lean_object* v_res_3502_;
v_res_3502_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3488_, v_argsPacker_3489_, v_e_3490_, lean_box(0), lean_box(0), v_a_3493_, v_b_3494_, lean_box(0), v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
stack->m_obj
 = v_res_3502_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object* v_upperBound_3503_, lean_object* v_argsPacker_3504_, lean_object* v_e_3505_, lean_object* v_inst_3506_, lean_object* v_R_3507_, lean_object* v_a_3508_, lean_object* v_b_3509_, lean_object* v_c_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3503_, v_argsPacker_3504_, v_e_3505_, v_inst_3506_, v_R_3507_, v_a_3508_, v_b_3509_, v_c_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v_argsPacker_3504_);
lean_dec(v_upperBound_3503_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object* v_a_3517_, lean_object* v_argsPacker_3518_, lean_object* v_name_3519_, lean_object* v_k_3520_, lean_object* v_tail_3521_, lean_object* v_x_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3517_, v_argsPacker_3518_, v_name_3519_, v_k_3520_, v_tail_3521_, v_x_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
return v_res_3528_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object* v_argsPacker_3529_, lean_object* v_name_3530_, lean_object* v_k_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
if (lean_obj_tag(v_a_3532_) == 0)
{
lean_object* v___x_3539_; 
lean_dec(v_name_3530_);
lean_dec_ref(v_argsPacker_3529_);
lean_inc(v_a_3537_);
lean_inc_ref(v_a_3536_);
lean_inc(v_a_3535_);
lean_inc_ref(v_a_3534_);
v___x_3539_ = lean_apply_6(v_k_3531_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, lean_box(0));
return v___x_3539_;
}
else
{
lean_object* v_head_3540_; lean_object* v_tail_3541_; lean_object* v___f_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_head_3540_ = lean_ctor_get(v_a_3532_, 0);
lean_inc(v_head_3540_);
v_tail_3541_ = lean_ctor_get(v_a_3532_, 1);
lean_inc(v_tail_3541_);
lean_dec_ref_known(v_a_3532_, 2);
lean_inc(v_name_3530_);
lean_inc_ref(v_argsPacker_3529_);
lean_inc_ref(v_a_3533_);
v___f_3542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3542_, 0, v_a_3533_);
lean_closure_set(v___f_3542_, 1, v_argsPacker_3529_);
lean_closure_set(v___f_3542_, 2, v_name_3530_);
lean_closure_set(v___f_3542_, 3, v_k_3531_);
lean_closure_set(v___f_3542_, 4, v_tail_3541_);
v___x_3543_ = lean_array_get_size(v_argsPacker_3529_);
lean_dec_ref(v_argsPacker_3529_);
v___x_3544_ = lean_unsigned_to_nat(1u);
v___x_3545_ = lean_nat_dec_eq(v___x_3543_, v___x_3544_);
if (v___x_3545_ == 0)
{
uint8_t v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3546_ = 1;
v___x_3547_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3530_, v___x_3546_);
v___x_3548_ = lean_array_get_size(v_a_3533_);
lean_dec_ref(v_a_3533_);
v___x_3549_ = lean_nat_add(v___x_3548_, v___x_3544_);
v___x_3550_ = l_Nat_reprFast(v___x_3549_);
v___x_3551_ = lean_string_append(v___x_3547_, v___x_3550_);
lean_dec_ref(v___x_3550_);
v___x_3552_ = lean_box(0);
v___x_3553_ = l_Lean_Name_str___override(v___x_3552_, v___x_3551_);
v___x_3554_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3553_, v_head_3540_, v___f_3542_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
return v___x_3554_;
}
else
{
lean_object* v___x_3555_; 
lean_dec_ref(v_a_3533_);
v___x_3555_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_3530_, v_head_3540_, v___f_3542_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
return v___x_3555_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3529_ = stack[0].m_obj;
lean_object* v_name_3530_ = stack[1].m_obj;
lean_object* v_k_3531_ = stack[2].m_obj;
lean_object* v_a_3532_ = stack[3].m_obj;
lean_object* v_a_3533_ = stack[4].m_obj;
lean_object* v_a_3534_ = stack[5].m_obj;
lean_object* v_a_3535_ = stack[6].m_obj;
lean_object* v_a_3536_ = stack[7].m_obj;
lean_object* v_a_3537_ = stack[8].m_obj;
lean_object* v_res_3556_;
v_res_3556_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3529_, v_name_3530_, v_k_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
stack->m_obj
 = v_res_3556_;
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object* v_a_3557_, lean_object* v_argsPacker_3558_, lean_object* v_name_3559_, lean_object* v_k_3560_, lean_object* v_tail_3561_, lean_object* v_x_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_array_push(v_a_3557_, v_x_3562_);
v___x_3569_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3558_, v_name_3559_, v_k_3560_, v_tail_3561_, v___x_3568_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
return v___x_3569_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3557_ = stack[0].m_obj;
lean_object* v_argsPacker_3558_ = stack[1].m_obj;
lean_object* v_name_3559_ = stack[2].m_obj;
lean_object* v_k_3560_ = stack[3].m_obj;
lean_object* v_tail_3561_ = stack[4].m_obj;
lean_object* v_x_3562_ = stack[5].m_obj;
lean_object* v___y_3563_ = stack[6].m_obj;
lean_object* v___y_3564_ = stack[7].m_obj;
lean_object* v___y_3565_ = stack[8].m_obj;
lean_object* v___y_3566_ = stack[9].m_obj;
lean_object* v_res_3570_;
v_res_3570_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3557_, v_argsPacker_3558_, v_name_3559_, v_k_3560_, v_tail_3561_, v_x_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
stack->m_obj
 = v_res_3570_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object* v_argsPacker_3571_, lean_object* v_name_3572_, lean_object* v_k_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3571_, v_name_3572_, v_k_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
return v_res_3581_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object* v_00_u03b1_3582_, lean_object* v_argsPacker_3583_, lean_object* v_name_3584_, lean_object* v_k_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3583_, v_name_3584_, v_k_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
return v___x_3593_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3583_ = stack[1].m_obj;
lean_object* v_name_3584_ = stack[2].m_obj;
lean_object* v_k_3585_ = stack[3].m_obj;
lean_object* v_a_3586_ = stack[4].m_obj;
lean_object* v_a_3587_ = stack[5].m_obj;
lean_object* v_a_3588_ = stack[6].m_obj;
lean_object* v_a_3589_ = stack[7].m_obj;
lean_object* v_a_3590_ = stack[8].m_obj;
lean_object* v_a_3591_ = stack[9].m_obj;
lean_object* v_res_3594_;
v_res_3594_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_box(0), v_argsPacker_3583_, v_name_3584_, v_k_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
stack->m_obj
 = v_res_3594_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object* v_00_u03b1_3595_, lean_object* v_argsPacker_3596_, lean_object* v_name_3597_, lean_object* v_k_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(v_00_u03b1_3595_, v_argsPacker_3596_, v_name_3597_, v_k_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
return v_res_3606_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object* v_argsPacker_3607_, lean_object* v_name_3608_, lean_object* v_type_3609_, lean_object* v_k_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3607_, v_type_3609_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = lean_array_to_list(v_a_3617_);
v___x_3619_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3620_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3607_, v_name_3608_, v_k_3610_, v___x_3618_, v___x_3619_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
return v___x_3620_;
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec_ref(v_k_3610_);
lean_dec(v_name_3608_);
lean_dec_ref(v_argsPacker_3607_);
v_a_3621_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3616_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3616_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3607_ = stack[0].m_obj;
lean_object* v_name_3608_ = stack[1].m_obj;
lean_object* v_type_3609_ = stack[2].m_obj;
lean_object* v_k_3610_ = stack[3].m_obj;
lean_object* v_a_3611_ = stack[4].m_obj;
lean_object* v_a_3612_ = stack[5].m_obj;
lean_object* v_a_3613_ = stack[6].m_obj;
lean_object* v_a_3614_ = stack[7].m_obj;
lean_object* v_res_3629_;
v_res_3629_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3607_, v_name_3608_, v_type_3609_, v_k_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
stack->m_obj
 = v_res_3629_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object* v_argsPacker_3630_, lean_object* v_name_3631_, lean_object* v_type_3632_, lean_object* v_k_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3630_, v_name_3631_, v_type_3632_, v_k_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
lean_dec(v_a_3637_);
lean_dec_ref(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec_ref(v_a_3634_);
return v_res_3639_;
}
}
lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object* v_00_u03b1_3640_, lean_object* v_argsPacker_3641_, lean_object* v_name_3642_, lean_object* v_type_3643_, lean_object* v_k_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3641_, v_name_3642_, v_type_3643_, v_k_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
return v___x_3650_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3641_ = stack[1].m_obj;
lean_object* v_name_3642_ = stack[2].m_obj;
lean_object* v_type_3643_ = stack[3].m_obj;
lean_object* v_k_3644_ = stack[4].m_obj;
lean_object* v_a_3645_ = stack[5].m_obj;
lean_object* v_a_3646_ = stack[6].m_obj;
lean_object* v_a_3647_ = stack[7].m_obj;
lean_object* v_a_3648_ = stack[8].m_obj;
lean_object* v_res_3651_;
v_res_3651_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_box(0), v_argsPacker_3641_, v_name_3642_, v_type_3643_, v_k_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
stack->m_obj
 = v_res_3651_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object* v_00_u03b1_3652_, lean_object* v_argsPacker_3653_, lean_object* v_name_3654_, lean_object* v_type_3655_, lean_object* v_k_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(v_00_u03b1_3652_, v_argsPacker_3653_, v_name_3654_, v_type_3655_, v_k_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
return v_res_3662_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object* v_argsPacker_3663_, lean_object* v_packedMotiveType_3664_, lean_object* v_type_3665_, lean_object* v_value_3666_, lean_object* v_k_3667_, lean_object* v_motives_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3663_, v_packedMotiveType_3664_, v_motives_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
lean_inc_n(v_a_3675_, 2);
lean_dec_ref_known(v___x_3674_, 1);
v___x_3676_ = lean_unsigned_to_nat(1u);
v___x_3677_ = lean_mk_empty_array_with_capacity(v___x_3676_);
v___x_3678_ = lean_array_push(v___x_3677_, v_a_3675_);
v___x_3679_ = l_Lean_Meta_instantiateForall(v_type_3665_, v___x_3678_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec_ref(v___x_3678_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v___x_3681_ = l_Lean_Expr_app___override(v_value_3666_, v_a_3675_);
lean_inc(v___y_3672_);
lean_inc_ref(v___y_3671_);
lean_inc(v___y_3670_);
lean_inc_ref(v___y_3669_);
v___x_3682_ = lean_apply_8(v_k_3667_, v_motives_3668_, v___x_3681_, v_a_3680_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, lean_box(0));
return v___x_3682_;
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_a_3675_);
lean_dec_ref(v_motives_3668_);
lean_dec_ref(v_k_3667_);
lean_dec_ref(v_value_3666_);
v_a_3683_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3679_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3679_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v_motives_3668_);
lean_dec_ref(v_k_3667_);
lean_dec_ref(v_value_3666_);
lean_dec_ref(v_type_3665_);
v_a_3691_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3674_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3674_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3663_ = stack[0].m_obj;
lean_object* v_packedMotiveType_3664_ = stack[1].m_obj;
lean_object* v_type_3665_ = stack[2].m_obj;
lean_object* v_value_3666_ = stack[3].m_obj;
lean_object* v_k_3667_ = stack[4].m_obj;
lean_object* v_motives_3668_ = stack[5].m_obj;
lean_object* v___y_3669_ = stack[6].m_obj;
lean_object* v___y_3670_ = stack[7].m_obj;
lean_object* v___y_3671_ = stack[8].m_obj;
lean_object* v___y_3672_ = stack[9].m_obj;
lean_object* v_res_3699_;
v_res_3699_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3663_, v_packedMotiveType_3664_, v_type_3665_, v_value_3666_, v_k_3667_, v_motives_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
stack->m_obj
 = v_res_3699_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object* v_argsPacker_3700_, lean_object* v_packedMotiveType_3701_, lean_object* v_type_3702_, lean_object* v_value_3703_, lean_object* v_k_3704_, lean_object* v_motives_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3700_, v_packedMotiveType_3701_, v_type_3702_, v_value_3703_, v_k_3704_, v_motives_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_argsPacker_3700_);
return v_res_3711_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0));
v___x_3714_ = l_Lean_stringToMessageData(v___x_3713_);
return v___x_3714_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2));
v___x_3717_ = l_Lean_stringToMessageData(v___x_3716_);
return v___x_3717_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object* v_argsPacker_3718_, lean_object* v_value_3719_, lean_object* v_type_3720_, lean_object* v_k_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; uint8_t v___x_3756_; 
v___x_3756_ = l_Lean_Expr_isForall(v_type_3720_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec_ref(v_k_3721_);
lean_dec_ref(v_value_3719_);
lean_dec_ref(v_argsPacker_3718_);
v___x_3757_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3);
v___x_3758_ = l_Lean_MessageData_ofExpr(v_type_3720_);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3759_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_);
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
v___y_3737_ = v_a_3722_;
v___y_3738_ = v_a_3723_;
v___y_3739_ = v_a_3724_;
v___y_3740_ = v_a_3725_;
goto v___jp_3736_;
}
v___jp_3727_:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = l_Lean_Expr_bindingName_x21(v_type_3720_);
lean_dec_ref(v_type_3720_);
v___x_3735_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3718_, v___x_3734_, v___y_3729_, v___y_3728_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
return v___x_3735_;
}
v___jp_3736_:
{
lean_object* v_packedMotiveType_3741_; lean_object* v___f_3742_; uint8_t v___x_3743_; 
v_packedMotiveType_3741_ = l_Lean_Expr_bindingDomain_x21(v_type_3720_);
lean_inc_ref(v_type_3720_);
lean_inc_ref(v_packedMotiveType_3741_);
lean_inc_ref(v_argsPacker_3718_);
v___f_3742_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3742_, 0, v_argsPacker_3718_);
lean_closure_set(v___f_3742_, 1, v_packedMotiveType_3741_);
lean_closure_set(v___f_3742_, 2, v_type_3720_);
lean_closure_set(v___f_3742_, 3, v_value_3719_);
lean_closure_set(v___f_3742_, 4, v_k_3721_);
v___x_3743_ = l_Lean_Expr_isForall(v_packedMotiveType_3741_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec_ref(v___f_3742_);
lean_dec_ref(v_type_3720_);
lean_dec_ref(v_argsPacker_3718_);
v___x_3744_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1);
v___x_3745_ = l_Lean_indentExpr(v_packedMotiveType_3741_);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3746_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
else
{
v___y_3728_ = v___f_3742_;
v___y_3729_ = v_packedMotiveType_3741_;
v___y_3730_ = v___y_3737_;
v___y_3731_ = v___y_3738_;
v___y_3732_ = v___y_3739_;
v___y_3733_ = v___y_3740_;
goto v___jp_3727_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_curryParam___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3718_ = stack[0].m_obj;
lean_object* v_value_3719_ = stack[1].m_obj;
lean_object* v_type_3720_ = stack[2].m_obj;
lean_object* v_k_3721_ = stack[3].m_obj;
lean_object* v_a_3722_ = stack[4].m_obj;
lean_object* v_a_3723_ = stack[5].m_obj;
lean_object* v_a_3724_ = stack[6].m_obj;
lean_object* v_a_3725_ = stack[7].m_obj;
lean_object* v_res_3769_;
v_res_3769_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3718_, v_value_3719_, v_type_3720_, v_k_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_);
stack->m_obj
 = v_res_3769_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object* v_argsPacker_3770_, lean_object* v_value_3771_, lean_object* v_type_3772_, lean_object* v_k_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3770_, v_value_3771_, v_type_3772_, v_k_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
return v_res_3779_;
}
}
lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object* v_00_u03b1_3780_, lean_object* v_argsPacker_3781_, lean_object* v_value_3782_, lean_object* v_type_3783_, lean_object* v_k_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3781_, v_value_3782_, v_type_3783_, v_k_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT void l_Lean_Meta_ArgsPacker_curryParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_argsPacker_3781_ = stack[1].m_obj;
lean_object* v_value_3782_ = stack[2].m_obj;
lean_object* v_type_3783_ = stack[3].m_obj;
lean_object* v_k_3784_ = stack[4].m_obj;
lean_object* v_a_3785_ = stack[5].m_obj;
lean_object* v_a_3786_ = stack[6].m_obj;
lean_object* v_a_3787_ = stack[7].m_obj;
lean_object* v_a_3788_ = stack[8].m_obj;
lean_object* v_res_3791_;
v_res_3791_ = l_Lean_Meta_ArgsPacker_curryParam(lean_box(0), v_argsPacker_3781_, v_value_3782_, v_type_3783_, v_k_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_);
stack->m_obj
 = v_res_3791_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object* v_00_u03b1_3792_, lean_object* v_argsPacker_3793_, lean_object* v_value_3794_, lean_object* v_type_3795_, lean_object* v_k_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Meta_ArgsPacker_curryParam(v_00_u03b1_3792_, v_argsPacker_3793_, v_value_3794_, v_type_3795_, v_k_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
lean_dec_ref(v_a_3797_);
return v_res_3802_;
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
