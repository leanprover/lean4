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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_ArgsPacker_Mutual_packType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___closed__0 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_packType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_packType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1 = (const lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Mutual.unpackType: Expected PSum type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: args.size == 2\n    "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.ArgsPacker.Mutual.pack"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__2;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_packType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(201, 156, 94, 164, 220, 114, 107, 70)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__5_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_packType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(14, 217, 178, 28, 107, 212, 157, 131)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_packType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: xType.isAppOfArity ``PSum 2\n    "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Meta.ArgsPacker.0.Lean.Meta.ArgsPacker.Mutual.mkCodomain.go"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Mutual.casesOn: Expected PSum type, got "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Mutual.casesOn: no alternatives"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1___boxed(lean_object**);
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
uint8_t v___x_2868__boxed_711_; uint8_t v___x_2869__boxed_712_; uint8_t v___x_2870__boxed_713_; lean_object* v_res_714_; 
v___x_2868__boxed_711_ = lean_unbox(v___x_701_);
v___x_2869__boxed_712_ = lean_unbox(v___x_702_);
v___x_2870__boxed_713_ = lean_unbox(v___x_703_);
v_res_714_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1(v___x_692_, v___x_693_, v___x_694_, v_arg_695_, v_arg_696_, v_a_697_, v_alt_698_, v_tail_699_, v_u_700_, v___x_2868__boxed_711_, v___x_2869__boxed_712_, v___x_2870__boxed_713_, v_head_704_, v_x_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
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
lean_dec(v_a_753_);
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
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_754_);
v___x_757_ = l_Lean_Expr_isApp(v___x_756_);
if (v___x_757_ == 0)
{
lean_dec_ref(v___x_756_);
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
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_756_);
v___x_759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__0));
v___x_760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_761_ = l_Lean_Expr_isConstOf(v___x_758_, v___x_760_);
lean_dec_ref(v___x_758_);
if (v___x_761_ == 0)
{
lean_dec_ref(v___x_756_);
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
lean_object* v_arg_762_; lean_object* v_arg_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; 
v_arg_762_ = lean_ctor_get(v___x_754_, 1);
lean_inc_ref(v_arg_762_);
lean_dec_ref(v___x_754_);
v_arg_763_ = lean_ctor_get(v___x_756_, 1);
lean_inc_ref(v_arg_763_);
lean_dec_ref(v___x_756_);
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
v___x_771_ = l_Lean_Meta_mkLambdaFVars(v___x_768_, v_codomain_722_, v___x_769_, v___x_761_, v___x_769_, v___x_761_, v___x_770_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec_ref(v___x_768_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_n(v_a_772_, 2);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = lean_box(v___x_769_);
v___x_774_ = lean_box(v___x_761_);
v___x_775_ = lean_box(v___x_770_);
lean_inc(v_u_721_);
lean_inc_ref(v_arg_762_);
lean_inc_ref_n(v_arg_763_, 2);
lean_inc(v___x_765_);
v___f_776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__1___boxed), 19, 13);
lean_closure_set(v___f_776_, 0, v___x_767_);
lean_closure_set(v___f_776_, 1, v___x_759_);
lean_closure_set(v___f_776_, 2, v___x_765_);
lean_closure_set(v___f_776_, 3, v_arg_763_);
lean_closure_set(v___f_776_, 4, v_arg_762_);
lean_closure_set(v___f_776_, 5, v_a_772_);
lean_closure_set(v___f_776_, 6, v_alt_723_);
lean_closure_set(v___f_776_, 7, v_tail_730_);
lean_closure_set(v___f_776_, 8, v_u_721_);
lean_closure_set(v___f_776_, 9, v___x_773_);
lean_closure_set(v___f_776_, 10, v___x_774_);
lean_closure_set(v___f_776_, 11, v___x_775_);
lean_closure_set(v___f_776_, 12, v_head_740_);
v___x_777_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_736_, v_arg_763_, v___f_776_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
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
v___x_786_ = l_Lean_mkApp5(v___x_785_, v_arg_763_, v_arg_762_, v_a_772_, v_e_720_, v_a_778_);
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
lean_dec_ref(v_arg_763_);
lean_dec_ref(v_arg_762_);
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
lean_dec_ref(v_arg_763_);
lean_dec_ref(v_arg_762_);
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
lean_dec(v_head_736_);
lean_dec_ref_known(v_tail_730_, 2);
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
uint8_t v___x_2889__boxed_848_; uint8_t v___x_2890__boxed_849_; uint8_t v___x_2891__boxed_850_; lean_object* v_res_851_; 
v___x_2889__boxed_848_ = lean_unbox(v___x_839_);
v___x_2890__boxed_849_ = lean_unbox(v___x_840_);
v___x_2891__boxed_850_ = lean_unbox(v___x_841_);
v_res_851_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___lam__0(v___x_828_, v___x_829_, v_arg_830_, v_arg_831_, v_x_832_, v___x_833_, v_a_834_, v_alt_835_, v___x_836_, v_tail_837_, v_u_838_, v___x_2889__boxed_848_, v___x_2890__boxed_849_, v___x_2891__boxed_850_, v_y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
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
uint8_t v___x_615__boxed_1053_; lean_object* v_res_1054_; 
v___x_615__boxed_1053_ = lean_unbox(v___x_1046_);
v_res_1054_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1(v_arg_1041_, v_args_1042_, v_type_1043_, v_packedDomain_1044_, v_tail_1045_, v___x_615__boxed_1053_, v_x_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
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
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1084_);
v___x_1087_ = l_Lean_Expr_isApp(v___x_1086_);
if (v___x_1087_ == 0)
{
lean_dec_ref(v___x_1086_);
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
lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1086_);
v___x_1089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1090_ = l_Lean_Expr_isConstOf(v___x_1088_, v___x_1089_);
lean_dec_ref(v___x_1088_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v___x_1086_);
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
lean_object* v_arg_1091_; lean_object* v_arg_1092_; lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; 
lean_dec_ref(v_domain_1057_);
v_arg_1091_ = lean_ctor_get(v___x_1084_, 1);
lean_inc_ref(v_arg_1091_);
lean_dec_ref(v___x_1084_);
v_arg_1092_ = lean_ctor_get(v___x_1086_, 1);
lean_inc_ref(v_arg_1092_);
lean_dec_ref(v___x_1086_);
v___x_1093_ = lean_box(v___x_1090_);
v___f_1094_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1094_, 0, v_arg_1091_);
lean_closure_set(v___f_1094_, 1, v_args_1058_);
lean_closure_set(v___f_1094_, 2, v_type_1055_);
lean_closure_set(v___f_1094_, 3, v_packedDomain_1056_);
lean_closure_set(v___f_1094_, 4, v_tail_1079_);
lean_closure_set(v___f_1094_, 5, v___x_1093_);
v___x_1095_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1083_, v_arg_1092_, v___f_1094_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
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
uint8_t v___x_733__boxed_1216_; lean_object* v_res_1217_; 
v___x_733__boxed_1216_ = lean_unbox(v___x_1209_);
v_res_1217_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1(v_arg_1204_, v_args_1205_, v_e_1206_, v_packedDomain_1207_, v_tail_1208_, v___x_733__boxed_1216_, v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
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
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1248_);
v___x_1251_ = l_Lean_Expr_isApp(v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec_ref(v___x_1250_);
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
lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1252_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1250_);
v___x_1253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ArgsPacker_Unary_packType_spec__0___closed__1));
v___x_1254_ = l_Lean_Expr_isConstOf(v___x_1252_, v___x_1253_);
lean_dec_ref(v___x_1252_);
if (v___x_1254_ == 0)
{
lean_dec_ref(v___x_1250_);
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
lean_object* v_arg_1255_; lean_object* v_arg_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; 
lean_dec_ref(v_domain_1220_);
v_arg_1255_ = lean_ctor_get(v___x_1248_, 1);
lean_inc_ref(v_arg_1255_);
lean_dec_ref(v___x_1248_);
v_arg_1256_ = lean_ctor_get(v___x_1250_, 1);
lean_inc_ref(v_arg_1256_);
lean_dec_ref(v___x_1250_);
v___x_1257_ = lean_box(v___x_1254_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry_go___lam__1___boxed), 12, 6);
lean_closure_set(v___f_1258_, 0, v_arg_1255_);
lean_closure_set(v___f_1258_, 1, v_args_1221_);
lean_closure_set(v___f_1258_, 2, v_e_1218_);
lean_closure_set(v___f_1258_, 3, v_packedDomain_1219_);
lean_closure_set(v___f_1258_, 4, v_tail_1243_);
lean_closure_set(v___f_1258_, 5, v___x_1257_);
v___x_1259_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_head_1247_, v_arg_1256_, v___f_1258_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(lean_object* v_n_1347_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_shiftr(v_n_1347_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft___boxed(lean_object* v_n_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v_n_1350_);
lean_dec(v_n_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType(lean_object* v_ds_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1361_ = lean_array_get_size(v_ds_1355_);
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_dec_le(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v_k_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_k_1364_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v___x_1361_);
v___x_1365_ = lean_unsigned_to_nat(0u);
lean_inc(v_k_1364_);
v___x_1366_ = l_Array_extract___redArg(v_ds_1355_, v___x_1365_, v_k_1364_);
v___x_1367_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_1366_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec_ref(v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v___x_1369_ = l_Array_extract___redArg(v_ds_1355_, v_k_1364_, v___x_1361_);
v___x_1370_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_1369_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec_ref(v___x_1369_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
v___x_1372_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1));
v___x_1373_ = lean_unsigned_to_nat(2u);
v___x_1374_ = lean_mk_empty_array_with_capacity(v___x_1373_);
v___x_1375_ = lean_array_push(v___x_1374_, v_a_1368_);
v___x_1376_ = lean_array_push(v___x_1375_, v_a_1371_);
v___x_1377_ = l_Lean_Meta_mkAppM(v___x_1372_, v___x_1376_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
return v___x_1377_;
}
else
{
lean_dec(v_a_1368_);
return v___x_1370_;
}
}
else
{
lean_dec(v_k_1364_);
return v___x_1367_;
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1378_ = l_Lean_instInhabitedExpr;
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_array_get_borrowed(v___x_1378_, v_ds_1355_, v___x_1379_);
lean_inc(v___x_1380_);
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_packType___boxed(lean_object* v_ds_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v_ds_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec_ref(v_ds_1382_);
return v_res_1388_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__0));
v___x_1391_ = l_Lean_stringToMessageData(v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(lean_object* v_n_1392_, lean_object* v_type_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_nat_dec_eq(v_n_1392_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = lean_nat_dec_eq(v_n_1392_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_inc_ref(v_type_1393_);
v___x_1412_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_1393_, v_a_1395_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = l_Lean_Expr_cleanupAnnotations(v_a_1413_);
lean_dec(v_a_1413_);
v___x_1415_ = l_Lean_Expr_isApp(v___x_1414_);
if (v___x_1415_ == 0)
{
lean_dec_ref(v___x_1414_);
v___y_1400_ = v_a_1394_;
v___y_1401_ = v_a_1395_;
v___y_1402_ = v_a_1396_;
v___y_1403_ = v_a_1397_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1414_);
v___x_1417_ = l_Lean_Expr_isApp(v___x_1416_);
if (v___x_1417_ == 0)
{
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1414_);
v___y_1400_ = v_a_1394_;
v___y_1401_ = v_a_1395_;
v___y_1402_ = v_a_1396_;
v___y_1403_ = v_a_1397_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1416_);
v___x_1419_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1));
v___x_1420_ = l_Lean_Expr_isConstOf(v___x_1418_, v___x_1419_);
lean_dec_ref(v___x_1418_);
if (v___x_1420_ == 0)
{
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1414_);
v___y_1400_ = v_a_1394_;
v___y_1401_ = v_a_1395_;
v___y_1402_ = v_a_1396_;
v___y_1403_ = v_a_1397_;
goto v___jp_1399_;
}
else
{
lean_object* v_arg_1421_; lean_object* v_arg_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec_ref(v_type_1393_);
v_arg_1421_ = lean_ctor_get(v___x_1414_, 1);
lean_inc_ref(v_arg_1421_);
lean_dec_ref(v___x_1414_);
v_arg_1422_ = lean_ctor_get(v___x_1416_, 1);
lean_inc_ref(v_arg_1422_);
lean_dec_ref(v___x_1416_);
v___x_1423_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v_n_1392_);
v___x_1424_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_1423_, v_arg_1422_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = lean_nat_sub(v_n_1392_, v___x_1423_);
lean_dec(v___x_1423_);
v___x_1427_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_1426_, v_arg_1421_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v___x_1426_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = l_List_appendTR___redArg(v_a_1425_, v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
else
{
lean_dec(v_a_1425_);
return v___x_1427_;
}
}
else
{
lean_dec(v___x_1423_);
lean_dec_ref(v_arg_1421_);
return v___x_1424_;
}
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v_type_1393_);
v_a_1437_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1412_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1412_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_type_1393_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_type_1393_);
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
v___jp_1399_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1404_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___closed__1);
v___x_1405_ = l_Lean_MessageData_ofExpr(v_type_1393_);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1406_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType___boxed(lean_object* v_n_1450_, lean_object* v_type_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_1450_, v_type_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_n_1450_);
return v_res_1457_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0(void){
_start:
{
lean_object* v___x_1458_; lean_object* v_dummy_1459_; 
v___x_1458_ = lean_box(0);
v_dummy_1459_ = l_Lean_Expr_sort___override(v___x_1458_);
return v_dummy_1459_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1462_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__1));
v___x_1463_ = lean_unsigned_to_nat(4u);
v___x_1464_ = lean_unsigned_to_nat(283u);
v___x_1465_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__0));
v___x_1466_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1467_ = l_mkPanicMessageWithDecl(v___x_1466_, v___x_1465_, v___x_1464_, v___x_1463_, v___x_1462_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0(lean_object* v_numFuncs_1476_, lean_object* v_fidx_1477_, lean_object* v_arg_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_x_1479_) == 5)
{
lean_object* v_fn_1488_; lean_object* v_arg_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_fn_1488_ = lean_ctor_get(v_x_1479_, 0);
lean_inc_ref(v_fn_1488_);
v_arg_1489_ = lean_ctor_get(v_x_1479_, 1);
lean_inc_ref(v_arg_1489_);
lean_dec_ref_known(v_x_1479_, 2);
v___x_1490_ = lean_array_set(v_x_1480_, v_x_1481_, v_arg_1489_);
v___x_1491_ = lean_nat_sub(v_x_1481_, v___x_1487_);
lean_dec(v_x_1481_);
v_x_1479_ = v_fn_1488_;
v_x_1480_ = v___x_1490_;
v_x_1481_ = v___x_1491_;
goto _start;
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
lean_dec(v_x_1481_);
v___x_1493_ = lean_array_get_size(v_x_1480_);
v___x_1494_ = lean_unsigned_to_nat(2u);
v___x_1495_ = lean_nat_dec_eq(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec_ref(v_x_1480_);
lean_dec_ref(v_x_1479_);
lean_dec_ref(v_arg_1478_);
v___x_1496_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__2);
v___x_1497_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1496_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = l_Lean_instInhabitedExpr;
v___x_1499_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v_numFuncs_1476_);
v___x_1500_ = lean_nat_dec_lt(v_fidx_1477_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1501_ = lean_nat_sub(v_numFuncs_1476_, v___x_1499_);
v___x_1502_ = lean_array_get(v___x_1498_, v_x_1480_, v___x_1487_);
v___x_1503_ = lean_nat_sub(v_fidx_1477_, v___x_1499_);
lean_dec(v___x_1499_);
lean_inc(v___x_1502_);
v___x_1504_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_1501_, v___x_1502_, v___x_1503_, v_arg_1478_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___x_1503_);
lean_dec(v___x_1501_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1518_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1518_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1518_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1509_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4));
v___x_1510_ = l_Lean_Expr_constLevels_x21(v_x_1479_);
lean_dec_ref(v_x_1479_);
v___x_1511_ = l_Lean_mkConst(v___x_1509_, v___x_1510_);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_array_get(v___x_1498_, v_x_1480_, v___x_1512_);
lean_dec_ref(v_x_1480_);
v___x_1514_ = l_Lean_mkApp3(v___x_1511_, v___x_1513_, v___x_1502_, v_a_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1514_);
v___x_1516_ = v___x_1507_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_dec(v___x_1502_);
lean_dec_ref(v_x_1480_);
lean_dec_ref(v_x_1479_);
return v___x_1504_;
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = lean_array_get(v___x_1498_, v_x_1480_, v___x_1519_);
lean_inc(v___x_1520_);
v___x_1521_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_1499_, v___x_1520_, v_fidx_1477_, v_arg_1478_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___x_1499_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1534_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1526_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6));
v___x_1527_ = l_Lean_Expr_constLevels_x21(v_x_1479_);
lean_dec_ref(v_x_1479_);
v___x_1528_ = l_Lean_mkConst(v___x_1526_, v___x_1527_);
v___x_1529_ = lean_array_get(v___x_1498_, v_x_1480_, v___x_1487_);
lean_dec_ref(v_x_1480_);
v___x_1530_ = l_Lean_mkApp3(v___x_1528_, v___x_1520_, v___x_1529_, v_a_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1530_);
v___x_1532_ = v___x_1524_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
lean_dec(v___x_1520_);
lean_dec_ref(v_x_1480_);
lean_dec_ref(v_x_1479_);
return v___x_1521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack(lean_object* v_numFuncs_1535_, lean_object* v_domain_1536_, lean_object* v_fidx_1537_, lean_object* v_arg_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = lean_unsigned_to_nat(1u);
v___x_1545_ = lean_nat_dec_le(v_numFuncs_1535_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Meta_whnfD(v_domain_1536_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v_dummy_1548_; lean_object* v_nargs_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v_dummy_1548_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0, &l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0_once, _init_l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0);
v_nargs_1549_ = l_Lean_Expr_getAppNumArgs(v_a_1547_);
lean_inc(v_nargs_1549_);
v___x_1550_ = lean_mk_array(v_nargs_1549_, v_dummy_1548_);
v___x_1551_ = lean_nat_sub(v_nargs_1549_, v___x_1544_);
lean_dec(v_nargs_1549_);
v___x_1552_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0(v_numFuncs_1535_, v_fidx_1537_, v_arg_1538_, v_a_1547_, v___x_1550_, v___x_1551_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
return v___x_1552_;
}
else
{
lean_dec_ref(v_arg_1538_);
return v___x_1546_;
}
}
else
{
lean_object* v___x_1553_; 
lean_dec_ref(v_domain_1536_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_arg_1538_);
return v___x_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_pack___boxed(lean_object* v_numFuncs_1554_, lean_object* v_domain_1555_, lean_object* v_fidx_1556_, lean_object* v_arg_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v_numFuncs_1554_, v_domain_1555_, v_fidx_1556_, v_arg_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_fidx_1556_);
lean_dec(v_numFuncs_1554_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___boxed(lean_object* v_numFuncs_1564_, lean_object* v_fidx_1565_, lean_object* v_arg_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0(v_numFuncs_1564_, v_fidx_1565_, v_arg_1566_, v_x_1567_, v_x_1568_, v_x_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v_fidx_1565_);
lean_dec(v_numFuncs_1564_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_unpack(lean_object* v_numFuncs_1576_, lean_object* v_e_1577_){
_start:
{
lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1578_ = lean_unsigned_to_nat(1u);
v___x_1579_ = lean_nat_dec_le(v_numFuncs_1576_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v_k_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_k_1580_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v_numFuncs_1576_);
v___x_1581_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6));
v___x_1582_ = lean_unsigned_to_nat(3u);
v___x_1583_ = l_Lean_Expr_isAppOfArity(v_e_1577_, v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4));
v___x_1585_ = l_Lean_Expr_isAppOfArity(v_e_1577_, v___x_1584_, v___x_1582_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec(v_k_1580_);
lean_dec_ref(v_e_1577_);
lean_dec(v_numFuncs_1576_);
v___x_1586_ = lean_box(0);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1587_ = lean_nat_sub(v_numFuncs_1576_, v_k_1580_);
lean_dec(v_numFuncs_1576_);
v___x_1588_ = lean_unsigned_to_nat(2u);
v___x_1589_ = l_Lean_Expr_getAppNumArgs(v_e_1577_);
v___x_1590_ = lean_nat_sub(v___x_1589_, v___x_1588_);
lean_dec(v___x_1589_);
v___x_1591_ = lean_nat_sub(v___x_1590_, v___x_1578_);
lean_dec(v___x_1590_);
v___x_1592_ = l_Lean_Expr_getRevArg_x21(v_e_1577_, v___x_1591_);
lean_dec_ref(v_e_1577_);
v___x_1593_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_1587_, v___x_1592_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_dec(v_k_1580_);
return v___x_1593_;
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1611_; 
v_val_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1611_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_val_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1611_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1610_; 
v_fst_1598_ = lean_ctor_get(v_val_1594_, 0);
v_snd_1599_ = lean_ctor_get(v_val_1594_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_val_1594_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1601_ = v_val_1594_;
v_isShared_1602_ = v_isSharedCheck_1610_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_snd_1599_);
lean_inc(v_fst_1598_);
lean_dec(v_val_1594_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1610_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_nat_add(v_k_1580_, v_fst_1598_);
lean_dec(v_fst_1598_);
lean_dec(v_k_1580_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1603_);
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_snd_1599_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1605_);
v___x_1607_ = v___x_1596_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v_numFuncs_1576_);
v___x_1612_ = lean_unsigned_to_nat(2u);
v___x_1613_ = l_Lean_Expr_getAppNumArgs(v_e_1577_);
v___x_1614_ = lean_nat_sub(v___x_1613_, v___x_1612_);
lean_dec(v___x_1613_);
v___x_1615_ = lean_nat_sub(v___x_1614_, v___x_1578_);
lean_dec(v___x_1614_);
v___x_1616_ = l_Lean_Expr_getRevArg_x21(v_e_1577_, v___x_1615_);
lean_dec_ref(v_e_1577_);
v_numFuncs_1576_ = v_k_1580_;
v_e_1577_ = v___x_1616_;
goto _start;
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec(v_numFuncs_1576_);
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v_e_1577_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn(lean_object* v_u_1624_, lean_object* v_xType_1625_, lean_object* v_x_1626_, lean_object* v_minor1_1627_, lean_object* v_minor2_1628_){
_start:
{
lean_object* v_r_u2081_1648_; uint8_t v___x_1649_; 
v_r_u2081_1648_ = l_Lean_Expr_bindingBody_x21(v_minor1_1627_);
v___x_1649_ = l_Lean_Expr_hasLooseBVars(v_r_u2081_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = l_Lean_Expr_bindingBody_x21(v_minor2_1628_);
v___x_1651_ = lean_expr_eqv(v_r_u2081_1648_, v___x_1650_);
lean_dec_ref(v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec_ref(v_r_u2081_1648_);
goto v___jp_1629_;
}
else
{
lean_dec_ref(v_minor2_1628_);
lean_dec_ref(v_minor1_1627_);
lean_dec_ref(v_x_1626_);
lean_dec_ref(v_xType_1625_);
lean_dec(v_u_1624_);
return v_r_u2081_1648_;
}
}
else
{
lean_dec_ref(v_r_u2081_1648_);
goto v___jp_1629_;
}
v___jp_1629_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v_motive_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_dummy_1640_; lean_object* v_nargs_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1630_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
lean_inc(v_u_1624_);
v___x_1631_ = l_Lean_mkSort(v_u_1624_);
v___x_1632_ = 0;
lean_inc_ref(v_xType_1625_);
v_motive_1633_ = l_Lean_Expr_lam___override(v___x_1630_, v_xType_1625_, v___x_1631_, v___x_1632_);
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn___closed__0));
v___x_1635_ = l_Lean_Level_succ___override(v_u_1624_);
v___x_1636_ = l_Lean_Expr_getAppFn(v_xType_1625_);
v___x_1637_ = l_Lean_Expr_constLevels_x21(v___x_1636_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1635_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_mkConst(v___x_1634_, v___x_1638_);
v_dummy_1640_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0, &l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0_once, _init_l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0);
v_nargs_1641_ = l_Lean_Expr_getAppNumArgs(v_xType_1625_);
lean_inc(v_nargs_1641_);
v___x_1642_ = lean_mk_array(v_nargs_1641_, v_dummy_1640_);
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_sub(v_nargs_1641_, v___x_1643_);
lean_dec(v_nargs_1641_);
v___x_1645_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_xType_1625_, v___x_1642_, v___x_1644_);
v___x_1646_ = l_Lean_mkAppN(v___x_1639_, v___x_1645_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_Lean_mkApp4(v___x_1646_, v_motive_1633_, v_x_1626_, v_minor1_1627_, v_minor2_1628_);
return v___x_1647_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1));
v___x_1655_ = lean_unsigned_to_nat(4u);
v___x_1656_ = lean_unsigned_to_nat(330u);
v___x_1657_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0));
v___x_1658_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1659_ = l_mkPanicMessageWithDecl(v___x_1658_, v___x_1657_, v___x_1656_, v___x_1655_, v___x_1654_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object* v_types_1660_, lean_object* v_k_1661_, lean_object* v_u_1662_, lean_object* v___x_1663_, uint8_t v___x_1664_, uint8_t v___x_1665_, lean_object* v_x_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_unsigned_to_nat(0u);
v___x_1673_ = l_Array_extract___redArg(v_types_1660_, v___x_1672_, v_k_1661_);
lean_inc_ref(v_x_1666_);
v___x_1674_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_u_1662_, v___x_1673_, v_x_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
v___x_1676_ = lean_mk_empty_array_with_capacity(v___x_1663_);
v___x_1677_ = lean_array_push(v___x_1676_, v_x_1666_);
v___x_1678_ = 1;
v___x_1679_ = l_Lean_Meta_mkLambdaFVars(v___x_1677_, v_a_1675_, v___x_1664_, v___x_1665_, v___x_1664_, v___x_1665_, v___x_1678_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec_ref(v___x_1677_);
return v___x_1679_;
}
else
{
lean_dec_ref(v_x_1666_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object* v_types_1680_, lean_object* v_k_1681_, lean_object* v_u_1682_, lean_object* v___x_1683_, lean_object* v___x_1684_, lean_object* v___x_1685_, lean_object* v_x_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
uint8_t v___x_1463__boxed_1692_; uint8_t v___x_1464__boxed_1693_; lean_object* v_res_1694_; 
v___x_1463__boxed_1692_ = lean_unbox(v___x_1684_);
v___x_1464__boxed_1693_ = lean_unbox(v___x_1685_);
v_res_1694_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v_types_1680_, v_k_1681_, v_u_1682_, v___x_1683_, v___x_1463__boxed_1692_, v___x_1464__boxed_1693_, v_x_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___x_1683_);
lean_dec_ref(v_types_1680_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object* v_types_1695_, lean_object* v_k_1696_, lean_object* v___x_1697_, lean_object* v_u_1698_, lean_object* v___x_1699_, lean_object* v___x_1700_, lean_object* v___x_1701_, lean_object* v_x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v___x_1447__boxed_1708_; uint8_t v___x_1448__boxed_1709_; lean_object* v_res_1710_; 
v___x_1447__boxed_1708_ = lean_unbox(v___x_1700_);
v___x_1448__boxed_1709_ = lean_unbox(v___x_1701_);
v_res_1710_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_types_1695_, v_k_1696_, v___x_1697_, v_u_1698_, v___x_1699_, v___x_1447__boxed_1708_, v___x_1448__boxed_1709_, v_x_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___x_1699_);
lean_dec_ref(v_types_1695_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object* v_u_1711_, lean_object* v_types_1712_, lean_object* v_x_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1719_ = lean_array_get_size(v_types_1712_);
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = lean_nat_dec_le(v___x_1719_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v_k_1722_; lean_object* v___x_1723_; 
v_k_1722_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v___x_1719_);
lean_inc(v_a_1717_);
lean_inc_ref(v_a_1716_);
lean_inc(v_a_1715_);
lean_inc_ref(v_a_1714_);
lean_inc_ref(v_x_1713_);
v___x_1723_ = lean_infer_type(v_x_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = l_Lean_Meta_whnfD(v_a_1724_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1));
v___x_1728_ = lean_unsigned_to_nat(2u);
v___x_1729_ = l_Lean_Expr_isAppOfArity(v_a_1726_, v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_a_1726_);
lean_dec(v_k_1722_);
lean_dec_ref(v_x_1713_);
lean_dec_ref(v_types_1712_);
lean_dec(v_u_1711_);
v___x_1730_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
v___x_1731_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1730_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___f_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___f_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1732_ = lean_box(v___x_1721_);
v___x_1733_ = lean_box(v___x_1729_);
lean_inc_n(v_u_1711_, 2);
lean_inc(v_k_1722_);
lean_inc_ref(v_types_1712_);
v___f_1734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1734_, 0, v_types_1712_);
lean_closure_set(v___f_1734_, 1, v_k_1722_);
lean_closure_set(v___f_1734_, 2, v_u_1711_);
lean_closure_set(v___f_1734_, 3, v___x_1720_);
lean_closure_set(v___f_1734_, 4, v___x_1732_);
lean_closure_set(v___f_1734_, 5, v___x_1733_);
v___x_1735_ = lean_box(v___x_1721_);
v___x_1736_ = lean_box(v___x_1729_);
v___f_1737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1737_, 0, v_types_1712_);
lean_closure_set(v___f_1737_, 1, v_k_1722_);
lean_closure_set(v___f_1737_, 2, v___x_1719_);
lean_closure_set(v___f_1737_, 3, v_u_1711_);
lean_closure_set(v___f_1737_, 4, v___x_1720_);
lean_closure_set(v___f_1737_, 5, v___x_1735_);
lean_closure_set(v___f_1737_, 6, v___x_1736_);
v___x_1738_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_1739_ = l_Lean_Core_mkFreshUserName(v___x_1738_, v_a_1716_, v_a_1717_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = l_Lean_Expr_appFn_x21(v_a_1726_);
v___x_1742_ = l_Lean_Expr_appArg_x21(v___x_1741_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1740_, v___x_1742_, v___f_1734_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1745_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1745_ = l_Lean_Core_mkFreshUserName(v___x_1738_, v_a_1716_, v_a_1717_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = l_Lean_Expr_appArg_x21(v_a_1726_);
v___x_1748_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1746_, v___x_1747_, v___f_1737_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1757_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn(v_u_1711_, v_a_1726_, v_x_1713_, v_a_1744_, v_a_1749_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1753_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
else
{
lean_dec(v_a_1744_);
lean_dec(v_a_1726_);
lean_dec_ref(v_x_1713_);
lean_dec(v_u_1711_);
return v___x_1748_;
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_a_1744_);
lean_dec_ref(v___f_1737_);
lean_dec(v_a_1726_);
lean_dec_ref(v_x_1713_);
lean_dec(v_u_1711_);
v_a_1758_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1745_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1745_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
lean_dec_ref(v___f_1737_);
lean_dec(v_a_1726_);
lean_dec_ref(v_x_1713_);
lean_dec(v_u_1711_);
return v___x_1743_;
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v___f_1737_);
lean_dec_ref(v___f_1734_);
lean_dec(v_a_1726_);
lean_dec_ref(v_x_1713_);
lean_dec(v_u_1711_);
v_a_1766_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1739_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1739_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
else
{
lean_dec(v_k_1722_);
lean_dec_ref(v_x_1713_);
lean_dec_ref(v_types_1712_);
lean_dec(v_u_1711_);
return v___x_1725_;
}
}
else
{
lean_dec(v_k_1722_);
lean_dec_ref(v_x_1713_);
lean_dec_ref(v_types_1712_);
lean_dec(v_u_1711_);
return v___x_1723_;
}
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v_u_1711_);
v___x_1774_ = l_Lean_instInhabitedExpr;
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_array_get(v___x_1774_, v_types_1712_, v___x_1775_);
lean_dec_ref(v_types_1712_);
v___x_1777_ = l_Lean_Expr_bindingBody_x21(v___x_1776_);
lean_dec(v___x_1776_);
v___x_1778_ = lean_expr_instantiate1(v___x_1777_, v_x_1713_);
lean_dec_ref(v_x_1713_);
lean_dec_ref(v___x_1777_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object* v_types_1780_, lean_object* v_k_1781_, lean_object* v___x_1782_, lean_object* v_u_1783_, lean_object* v___x_1784_, uint8_t v___x_1785_, uint8_t v___x_1786_, lean_object* v_x_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = l_Array_extract___redArg(v_types_1780_, v_k_1781_, v___x_1782_);
lean_inc_ref(v_x_1787_);
v___x_1794_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_u_1783_, v___x_1793_, v_x_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = lean_mk_empty_array_with_capacity(v___x_1784_);
v___x_1797_ = lean_array_push(v___x_1796_, v_x_1787_);
v___x_1798_ = 1;
v___x_1799_ = l_Lean_Meta_mkLambdaFVars(v___x_1797_, v_a_1795_, v___x_1785_, v___x_1786_, v___x_1785_, v___x_1786_, v___x_1798_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec_ref(v___x_1797_);
return v___x_1799_;
}
else
{
lean_dec_ref(v_x_1787_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object* v_u_1800_, lean_object* v_types_1801_, lean_object* v_x_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_u_1800_, v_types_1801_, v_x_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object* v_x_1809_, lean_object* v_body_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_Meta_getLevel(v_body_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object* v_x_1817_, lean_object* v_body_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1817_, v_body_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v_x_1817_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object* v_types_1826_, lean_object* v_x_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; 
v___f_1833_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0));
v___x_1834_ = l_Lean_instInhabitedExpr;
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_array_get_borrowed(v___x_1834_, v_types_1826_, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1838_ = 0;
lean_inc(v___x_1836_);
v___x_1839_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_1836_, v___x_1837_, v___f_1833_, v___x_1838_, v___x_1838_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_a_1840_, v_types_1826_, v_x_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
return v___x_1841_;
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v_x_1827_);
lean_dec_ref(v_types_1826_);
v_a_1842_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1839_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1839_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object* v_types_1850_, lean_object* v_x_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1850_, v_x_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object* v_a_1858_, lean_object* v___x_1859_, uint8_t v___x_1860_, lean_object* v_x_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
lean_inc_ref(v_x_1861_);
v___x_1867_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_a_1858_, v_x_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = lean_mk_empty_array_with_capacity(v___x_1859_);
v___x_1870_ = lean_array_push(v___x_1869_, v_x_1861_);
v___x_1871_ = 1;
v___x_1872_ = 1;
v___x_1873_ = l_Lean_Meta_mkForallFVars(v___x_1870_, v_a_1868_, v___x_1860_, v___x_1871_, v___x_1871_, v___x_1872_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec_ref(v___x_1870_);
return v___x_1873_;
}
else
{
lean_dec_ref(v_x_1861_);
return v___x_1867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object* v_a_1874_, lean_object* v___x_1875_, lean_object* v___x_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v___x_1823__boxed_1883_; lean_object* v_res_1884_; 
v___x_1823__boxed_1883_ = lean_unbox(v___x_1876_);
v_res_1884_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1874_, v___x_1875_, v___x_1823__boxed_1883_, v_x_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___x_1875_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t v_sz_1885_, size_t v_i_1886_, lean_object* v_bs_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_usize_dec_lt(v_i_1886_, v_sz_1885_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_bs_1887_);
return v___x_1894_;
}
else
{
lean_object* v_v_1895_; lean_object* v___x_1896_; lean_object* v_bs_x27_1897_; lean_object* v___x_1898_; 
v_v_1895_ = lean_array_uget(v_bs_1887_, v_i_1886_);
v___x_1896_ = lean_unsigned_to_nat(0u);
v_bs_x27_1897_ = lean_array_uset(v_bs_1887_, v_i_1886_, v___x_1896_);
v___x_1898_ = l_Lean_Meta_whnfForall(v_v_1895_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = ((size_t)1ULL);
v___x_1901_ = lean_usize_add(v_i_1886_, v___x_1900_);
v___x_1902_ = lean_array_uset(v_bs_x27_1897_, v_i_1886_, v_a_1899_);
v_i_1886_ = v___x_1901_;
v_bs_1887_ = v___x_1902_;
goto _start;
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v_bs_x27_1897_);
v_a_1904_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1898_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1898_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object* v_sz_1912_, lean_object* v_i_1913_, lean_object* v_bs_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
size_t v_sz_boxed_1920_; size_t v_i_boxed_1921_; lean_object* v_res_1922_; 
v_sz_boxed_1920_ = lean_unbox_usize(v_sz_1912_);
lean_dec(v_sz_1912_);
v_i_boxed_1921_ = lean_unbox_usize(v_i_1913_);
lean_dec(v_i_1913_);
v_res_1922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_1920_, v_i_boxed_1921_, v_bs_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1922_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object* v_as_1926_, size_t v_i_1927_, size_t v_stop_1928_, lean_object* v_b_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_a_1936_; uint8_t v___x_1940_; 
v___x_1940_ = lean_usize_dec_eq(v_i_1927_, v_stop_1928_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = lean_array_uget_borrowed(v_as_1926_, v_i_1927_);
v___x_1942_ = l_Lean_Expr_isForall(v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1943_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
lean_inc(v___x_1941_);
v___x_1944_ = l_Lean_MessageData_ofExpr(v___x_1941_);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1945_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v_a_1936_ = v_a_1947_;
goto v___jp_1935_;
}
else
{
return v___x_1946_;
}
}
else
{
lean_object* v___x_1948_; 
v___x_1948_ = lean_box(0);
v_a_1936_ = v___x_1948_;
goto v___jp_1935_;
}
}
else
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_b_1929_);
return v___x_1949_;
}
v___jp_1935_:
{
size_t v___x_1937_; size_t v___x_1938_; 
v___x_1937_ = ((size_t)1ULL);
v___x_1938_ = lean_usize_add(v_i_1927_, v___x_1937_);
v_i_1927_ = v___x_1938_;
v_b_1929_ = v_a_1936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object* v_as_1950_, lean_object* v_i_1951_, lean_object* v_stop_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_i_boxed_1959_; size_t v_stop_boxed_1960_; lean_object* v_res_1961_; 
v_i_boxed_1959_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_stop_boxed_1960_ = lean_unbox_usize(v_stop_1952_);
lean_dec(v_stop_1952_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_1950_, v_i_boxed_1959_, v_stop_boxed_1960_, v_b_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_as_1950_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t v_sz_1962_, size_t v_i_1963_, lean_object* v_bs_1964_){
_start:
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_usize_dec_lt(v_i_1963_, v_sz_1962_);
if (v___x_1965_ == 0)
{
return v_bs_1964_;
}
else
{
lean_object* v_v_1966_; lean_object* v___x_1967_; lean_object* v_bs_x27_1968_; lean_object* v___x_1969_; size_t v___x_1970_; size_t v___x_1971_; lean_object* v___x_1972_; 
v_v_1966_ = lean_array_uget(v_bs_1964_, v_i_1963_);
v___x_1967_ = lean_unsigned_to_nat(0u);
v_bs_x27_1968_ = lean_array_uset(v_bs_1964_, v_i_1963_, v___x_1967_);
v___x_1969_ = l_Lean_Expr_bindingDomain_x21(v_v_1966_);
lean_dec(v_v_1966_);
v___x_1970_ = ((size_t)1ULL);
v___x_1971_ = lean_usize_add(v_i_1963_, v___x_1970_);
v___x_1972_ = lean_array_uset(v_bs_x27_1968_, v_i_1963_, v___x_1969_);
v_i_1963_ = v___x_1971_;
v_bs_1964_ = v___x_1972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object* v_sz_1974_, lean_object* v_i_1975_, lean_object* v_bs_1976_){
_start:
{
size_t v_sz_boxed_1977_; size_t v_i_boxed_1978_; lean_object* v_res_1979_; 
v_sz_boxed_1977_ = lean_unbox_usize(v_sz_1974_);
lean_dec(v_sz_1974_);
v_i_boxed_1978_ = lean_unbox_usize(v_i_1975_);
lean_dec(v_i_1975_);
v_res_1979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_1977_, v_i_boxed_1978_, v_bs_1976_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object* v_types_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = lean_array_get_size(v_types_1980_);
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_dec_eq(v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
size_t v_sz_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
v_sz_1989_ = lean_array_size(v_types_1980_);
v___x_1990_ = ((size_t)0ULL);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_1989_, v___x_1990_, v_types_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc_n(v_a_1992_, 2);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = lean_box(v___x_1988_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1994_, 0, v_a_1992_);
lean_closure_set(v___f_1994_, 1, v___x_1987_);
lean_closure_set(v___f_1994_, 2, v___x_1993_);
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = lean_array_get_size(v_a_1992_);
v___x_2014_ = lean_nat_dec_lt(v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
goto v___jp_1995_;
}
else
{
lean_object* v___x_2015_; size_t v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = lean_usize_of_nat(v___x_2013_);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_1992_, v___x_1990_, v___x_2016_, v___x_2015_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_dec_ref_known(v___x_2017_, 1);
goto v___jp_1995_;
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v___f_1994_);
lean_dec(v_a_1992_);
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
v___jp_1995_:
{
size_t v_sz_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_sz_1996_ = lean_array_size(v_a_1992_);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_1996_, v___x_1990_, v_a_1992_);
v___x_1998_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_1997_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
lean_dec_ref(v___x_1997_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2001_ = l_Lean_Core_mkFreshUserName(v___x_2000_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2002_, v_a_1999_, v___f_1994_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
return v___x_2003_;
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec(v_a_1999_);
lean_dec_ref(v___f_1994_);
v_a_2004_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2001_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2001_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_dec_ref(v___f_1994_);
return v___x_1998_;
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1991_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1991_);
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
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2034_ = l_Lean_instInhabitedExpr;
v___x_2035_ = lean_unsigned_to_nat(0u);
v___x_2036_ = lean_array_get(v___x_2034_, v_types_1980_, v___x_2035_);
lean_dec_ref(v_types_1980_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object* v_types_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
return v_res_2044_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2));
v___x_2050_ = l_Lean_stringToMessageData(v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object* v___x_2051_, lean_object* v_as_2052_, size_t v_i_2053_, size_t v_stop_2054_, lean_object* v_b_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_a_2062_; uint8_t v___x_2066_; 
v___x_2066_ = lean_usize_dec_eq(v_i_2053_, v_stop_2054_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_array_uget_borrowed(v_as_2052_, v_i_2053_);
lean_inc_ref(v___x_2051_);
lean_inc(v___x_2067_);
v___x_2068_ = l_Lean_Meta_isExprDefEq(v___x_2067_, v___x_2051_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; uint8_t v___x_2070_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v___x_2070_ = lean_unbox(v_a_2069_);
lean_dec(v_a_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2071_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
lean_inc(v___x_2067_);
v___x_2072_ = l_Lean_MessageData_ofExpr(v___x_2067_);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
lean_inc_ref(v___x_2051_);
v___x_2076_ = l_Lean_MessageData_ofExpr(v___x_2051_);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2077_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v_a_2062_ = v_a_2079_;
goto v___jp_2061_;
}
else
{
lean_dec_ref(v___x_2051_);
return v___x_2078_;
}
}
else
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_box(0);
v_a_2062_ = v___x_2080_;
goto v___jp_2061_;
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v___x_2051_);
v_a_2081_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2068_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2068_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2089_; 
lean_dec_ref(v___x_2051_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_b_2055_);
return v___x_2089_;
}
v___jp_2061_:
{
size_t v___x_2063_; size_t v___x_2064_; 
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2053_, v___x_2063_);
v_i_2053_ = v___x_2064_;
v_b_2055_ = v_a_2062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object* v___x_2090_, lean_object* v_as_2091_, lean_object* v_i_2092_, lean_object* v_stop_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
size_t v_i_boxed_2100_; size_t v_stop_boxed_2101_; lean_object* v_res_2102_; 
v_i_boxed_2100_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_stop_boxed_2101_ = lean_unbox_usize(v_stop_2093_);
lean_dec(v_stop_2093_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2090_, v_as_2091_, v_i_boxed_2100_, v_stop_boxed_2101_, v_b_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_as_2091_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t v_sz_2103_, size_t v_i_2104_, lean_object* v_bs_2105_){
_start:
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_usize_dec_lt(v_i_2104_, v_sz_2103_);
if (v___x_2106_ == 0)
{
return v_bs_2105_;
}
else
{
lean_object* v_v_2107_; lean_object* v___x_2108_; lean_object* v_bs_x27_2109_; lean_object* v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v_v_2107_ = lean_array_uget(v_bs_2105_, v_i_2104_);
v___x_2108_ = lean_unsigned_to_nat(0u);
v_bs_x27_2109_ = lean_array_uset(v_bs_2105_, v_i_2104_, v___x_2108_);
v___x_2110_ = l_Lean_Expr_bindingBody_x21(v_v_2107_);
lean_dec(v_v_2107_);
v___x_2111_ = ((size_t)1ULL);
v___x_2112_ = lean_usize_add(v_i_2104_, v___x_2111_);
v___x_2113_ = lean_array_uset(v_bs_x27_2109_, v_i_2104_, v___x_2110_);
v_i_2104_ = v___x_2112_;
v_bs_2105_ = v___x_2113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object* v_sz_2115_, lean_object* v_i_2116_, lean_object* v_bs_2117_){
_start:
{
size_t v_sz_boxed_2118_; size_t v_i_boxed_2119_; lean_object* v_res_2120_; 
v_sz_boxed_2118_ = lean_unbox_usize(v_sz_2115_);
lean_dec(v_sz_2115_);
v_i_boxed_2119_ = lean_unbox_usize(v_i_2116_);
lean_dec(v_i_2116_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_2118_, v_i_boxed_2119_, v_bs_2117_);
return v_res_2120_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0));
v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object* v_as_2124_, size_t v_i_2125_, size_t v_stop_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_a_2134_; uint8_t v___x_2138_; 
v___x_2138_ = lean_usize_dec_eq(v_i_2125_, v_stop_2126_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = lean_array_uget_borrowed(v_as_2124_, v_i_2125_);
v___x_2140_ = l_Lean_Expr_isArrow(v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
lean_inc(v___x_2139_);
v___x_2142_ = l_Lean_MessageData_ofExpr(v___x_2139_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2143_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v_a_2134_ = v_a_2145_;
goto v___jp_2133_;
}
else
{
return v___x_2144_;
}
}
else
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_box(0);
v_a_2134_ = v___x_2146_;
goto v___jp_2133_;
}
}
else
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_b_2127_);
return v___x_2147_;
}
v___jp_2133_:
{
size_t v___x_2135_; size_t v___x_2136_; 
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_add(v_i_2125_, v___x_2135_);
v_i_2125_ = v___x_2136_;
v_b_2127_ = v_a_2134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object* v_as_2148_, lean_object* v_i_2149_, lean_object* v_stop_2150_, lean_object* v_b_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
size_t v_i_boxed_2157_; size_t v_stop_boxed_2158_; lean_object* v_res_2159_; 
v_i_boxed_2157_ = lean_unbox_usize(v_i_2149_);
lean_dec(v_i_2149_);
v_stop_boxed_2158_ = lean_unbox_usize(v_stop_2150_);
lean_dec(v_stop_2150_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2148_, v_i_boxed_2157_, v_stop_boxed_2158_, v_b_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v_as_2148_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object* v_types_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; size_t v_sz_2167_; size_t v___x_2168_; lean_object* v___x_2169_; 
v___x_2166_ = l_Lean_instInhabitedExpr;
v_sz_2167_ = lean_array_size(v_types_2160_);
v___x_2168_ = ((size_t)0ULL);
v___x_2169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2167_, v___x_2168_, v_types_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___y_2173_; size_t v___y_2174_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2201_ = lean_array_get_size(v_a_2170_);
v___x_2202_ = lean_nat_dec_lt(v___x_2171_, v___x_2201_);
if (v___x_2202_ == 0)
{
goto v___jp_2180_;
}
else
{
lean_object* v___x_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_box(0);
v___x_2204_ = lean_usize_of_nat(v___x_2201_);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2170_, v___x_2168_, v___x_2204_, v___x_2203_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_dec_ref_known(v___x_2205_, 1);
goto v___jp_2180_;
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_a_2170_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
v___jp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_array_get(v___x_2166_, v___y_2173_, v___x_2171_);
lean_dec_ref(v___y_2173_);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_2174_, v___x_2168_, v_a_2170_);
v___x_2177_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2176_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec_ref(v___x_2176_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l_Lean_mkArrow(v_a_2178_, v___x_2175_, v_a_2163_, v_a_2164_);
return v___x_2179_;
}
else
{
lean_dec(v___x_2175_);
return v___x_2177_;
}
}
v___jp_2180_:
{
size_t v_sz_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v_sz_2181_ = lean_array_size(v_a_2170_);
lean_inc(v_a_2170_);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2181_, v___x_2168_, v_a_2170_);
v___x_2183_ = lean_array_get_size(v___x_2182_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_sub(v___x_2183_, v___x_2184_);
v___x_2186_ = lean_array_get_borrowed(v___x_2166_, v___x_2182_, v___x_2185_);
lean_dec(v___x_2185_);
lean_inc_ref(v___x_2182_);
v___x_2187_ = lean_array_pop(v___x_2182_);
v___x_2188_ = lean_array_get_size(v___x_2187_);
v___x_2189_ = lean_nat_dec_lt(v___x_2171_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_dec_ref(v___x_2187_);
v___y_2173_ = v___x_2182_;
v___y_2174_ = v_sz_2181_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2190_; size_t v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_box(0);
v___x_2191_ = lean_usize_of_nat(v___x_2188_);
lean_inc(v___x_2186_);
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2186_, v___x_2187_, v___x_2168_, v___x_2191_, v___x_2190_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec_ref(v___x_2187_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_dec_ref_known(v___x_2192_, 1);
v___y_2173_ = v___x_2182_;
v___y_2174_ = v_sz_2181_;
goto v___jp_2172_;
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v___x_2182_);
lean_dec(v_a_2170_);
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_a_2214_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2169_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2169_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object* v_types_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
return v_res_2228_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object* v_ctor_2232_, lean_object* v___x_2233_, lean_object* v_arg_2234_, lean_object* v_arg_2235_, lean_object* v___x_2236_, lean_object* v_a_2237_, lean_object* v_alts_2238_, lean_object* v___x_2239_, lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v_y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v___x_2330__boxed_2248_; uint8_t v___x_2331__boxed_2249_; uint8_t v___x_2332__boxed_2250_; lean_object* v_res_2251_; 
v___x_2330__boxed_2248_ = lean_unbox(v___x_2239_);
v___x_2331__boxed_2249_ = lean_unbox(v___x_2240_);
v___x_2332__boxed_2250_ = lean_unbox(v___x_2241_);
v_res_2251_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v_ctor_2232_, v___x_2233_, v_arg_2234_, v_arg_2235_, v___x_2236_, v_a_2237_, v_alts_2238_, v___x_2330__boxed_2248_, v___x_2331__boxed_2249_, v___x_2332__boxed_2250_, v_y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec_ref(v_alts_2238_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(lean_object* v___x_2252_, lean_object* v___x_2253_, lean_object* v_arg_2254_, lean_object* v_arg_2255_, lean_object* v___x_2256_, lean_object* v_a_2257_, uint8_t v___x_2258_, uint8_t v___x_2259_, uint8_t v___x_2260_, lean_object* v___x_2261_, lean_object* v_ctor_2262_, lean_object* v_d_2263_, lean_object* v_alts_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = lean_array_get_size(v_alts_2264_);
v___x_2271_ = lean_nat_dec_eq(v___x_2270_, v___x_2252_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2272_ = lean_box(v___x_2258_);
v___x_2273_ = lean_box(v___x_2259_);
v___x_2274_ = lean_box(v___x_2260_);
v___f_2275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2275_, 0, v_ctor_2262_);
lean_closure_set(v___f_2275_, 1, v___x_2253_);
lean_closure_set(v___f_2275_, 2, v_arg_2254_);
lean_closure_set(v___f_2275_, 3, v_arg_2255_);
lean_closure_set(v___f_2275_, 4, v___x_2256_);
lean_closure_set(v___f_2275_, 5, v_a_2257_);
lean_closure_set(v___f_2275_, 6, v_alts_2264_);
lean_closure_set(v___f_2275_, 7, v___x_2272_);
lean_closure_set(v___f_2275_, 8, v___x_2273_);
lean_closure_set(v___f_2275_, 9, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_2277_ = l_Lean_Core_mkFreshUserName(v___x_2276_, v___y_2267_, v___y_2268_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
v___x_2279_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2278_, v_d_2263_, v___f_2275_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2279_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v___f_2275_);
lean_dec_ref(v_d_2263_);
v_a_2280_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2277_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2277_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec_ref(v_d_2263_);
lean_dec(v_ctor_2262_);
lean_dec_ref(v_a_2257_);
lean_dec_ref(v___x_2256_);
lean_dec_ref(v_arg_2255_);
lean_dec_ref(v_arg_2254_);
lean_dec(v___x_2253_);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_array_get(v___x_2261_, v_alts_2264_, v___x_2288_);
lean_dec_ref(v_alts_2264_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object* v_x_2294_, lean_object* v_codomain_2295_, lean_object* v_alts_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___x_2312_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2312_ = l_Lean_instInhabitedExpr;
v___x_2378_ = lean_array_get_size(v_alts_2296_);
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_nat_dec_eq(v___x_2378_, v___x_2379_);
if (v___x_2380_ == 0)
{
v___y_2314_ = v_a_2297_;
v___y_2315_ = v_a_2298_;
v___y_2316_ = v_a_2299_;
v___y_2317_ = v_a_2300_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
v___x_2382_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2381_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_dec_ref_known(v___x_2382_, 1);
v___y_2314_ = v_a_2297_;
v___y_2315_ = v_a_2298_;
v___y_2316_ = v_a_2299_;
v___y_2317_ = v_a_2300_;
goto v___jp_2313_;
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v_codomain_2295_);
lean_dec_ref(v_x_2294_);
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
v___jp_2302_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2308_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
v___x_2309_ = l_Lean_MessageData_ofExpr(v___y_2303_);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2310_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
return v___x_2311_;
}
v___jp_2313_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2318_ = lean_array_get_size(v_alts_2296_);
v___x_2319_ = lean_unsigned_to_nat(1u);
v___x_2320_ = lean_nat_dec_eq(v___x_2318_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; 
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc(v___y_2315_);
lean_inc_ref(v___y_2314_);
lean_inc_ref(v_x_2294_);
v___x_2321_ = lean_infer_type(v_x_2294_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc_n(v_a_2322_, 2);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2322_, v___y_2315_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = l_Lean_Expr_cleanupAnnotations(v_a_2324_);
lean_dec(v_a_2324_);
v___x_2326_ = l_Lean_Expr_isApp(v___x_2325_);
if (v___x_2326_ == 0)
{
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_codomain_2295_);
lean_dec_ref(v_x_2294_);
v___y_2303_ = v_a_2322_;
v___y_2304_ = v___y_2314_;
v___y_2305_ = v___y_2315_;
v___y_2306_ = v___y_2316_;
v___y_2307_ = v___y_2317_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2325_);
v___x_2328_ = l_Lean_Expr_isApp(v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec_ref(v___x_2327_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_codomain_2295_);
lean_dec_ref(v_x_2294_);
v___y_2303_ = v_a_2322_;
v___y_2304_ = v___y_2314_;
v___y_2305_ = v___y_2315_;
v___y_2306_ = v___y_2316_;
v___y_2307_ = v___y_2317_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2327_);
v___x_2330_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1));
v___x_2331_ = l_Lean_Expr_isConstOf(v___x_2329_, v___x_2330_);
lean_dec_ref(v___x_2329_);
if (v___x_2331_ == 0)
{
lean_dec_ref(v___x_2327_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_codomain_2295_);
lean_dec_ref(v_x_2294_);
v___y_2303_ = v_a_2322_;
v___y_2304_ = v___y_2314_;
v___y_2305_ = v___y_2315_;
v___y_2306_ = v___y_2316_;
v___y_2307_ = v___y_2317_;
goto v___jp_2302_;
}
else
{
lean_object* v_arg_2332_; lean_object* v_arg_2333_; lean_object* v___x_2334_; 
v_arg_2332_ = lean_ctor_get(v___x_2325_, 1);
lean_inc_ref(v_arg_2332_);
lean_dec_ref(v___x_2325_);
v_arg_2333_ = lean_ctor_get(v___x_2327_, 1);
lean_inc_ref(v_arg_2333_);
lean_dec_ref(v___x_2327_);
lean_inc_ref(v_codomain_2295_);
v___x_2334_ = l_Lean_Meta_getLevel(v_codomain_2295_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_Expr_getAppFn(v_a_2322_);
lean_dec(v_a_2322_);
v___x_2337_ = l_Lean_Expr_constLevels_x21(v___x_2336_);
lean_dec_ref(v___x_2336_);
v___x_2338_ = lean_mk_empty_array_with_capacity(v___x_2319_);
lean_inc_ref(v_x_2294_);
lean_inc_ref(v___x_2338_);
v___x_2339_ = lean_array_push(v___x_2338_, v_x_2294_);
v___x_2340_ = 1;
v___x_2341_ = l_Lean_Meta_mkLambdaFVars(v___x_2339_, v_codomain_2295_, v___x_2320_, v___x_2331_, v___x_2320_, v___x_2331_, v___x_2340_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec_ref(v___x_2339_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_n(v_a_2342_, 2);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v___x_2318_);
v___x_2344_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6));
v___x_2345_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_2343_);
v___x_2346_ = l_Array_extract___redArg(v_alts_2296_, v___x_2345_, v___x_2343_);
lean_inc_ref(v___x_2338_);
lean_inc_ref(v_arg_2332_);
lean_inc_ref_n(v_arg_2333_, 2);
lean_inc(v___x_2337_);
v___x_2347_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(v___x_2319_, v___x_2337_, v_arg_2333_, v_arg_2332_, v___x_2338_, v_a_2342_, v___x_2320_, v___x_2331_, v___x_2340_, v___x_2312_, v___x_2344_, v_arg_2333_, v___x_2346_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4));
v___x_2350_ = l_Array_extract___redArg(v_alts_2296_, v___x_2343_, v___x_2318_);
lean_inc(v_a_2342_);
lean_inc_ref_n(v_arg_2332_, 2);
lean_inc_ref(v_arg_2333_);
lean_inc(v___x_2337_);
v___x_2351_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(v___x_2319_, v___x_2337_, v_arg_2333_, v_arg_2332_, v___x_2338_, v_a_2342_, v___x_2320_, v___x_2331_, v___x_2340_, v___x_2312_, v___x_2349_, v_arg_2332_, v___x_2350_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2363_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_mkCasesOn___closed__0));
v___x_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_a_2335_);
lean_ctor_set(v___x_2357_, 1, v___x_2337_);
v___x_2358_ = l_Lean_Expr_const___override(v___x_2356_, v___x_2357_);
v___x_2359_ = l_Lean_mkApp6(v___x_2358_, v_arg_2333_, v_arg_2332_, v_a_2342_, v_x_2294_, v_a_2348_, v_a_2352_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2359_);
v___x_2361_ = v___x_2354_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_dec(v_a_2348_);
lean_dec(v_a_2342_);
lean_dec(v___x_2337_);
lean_dec(v_a_2335_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_x_2294_);
return v___x_2351_;
}
}
else
{
lean_dec(v___x_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec(v_a_2335_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_x_2294_);
return v___x_2347_;
}
}
else
{
lean_dec_ref(v___x_2338_);
lean_dec(v___x_2337_);
lean_dec(v_a_2335_);
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2332_);
lean_dec_ref(v_x_2294_);
return v___x_2341_;
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v_arg_2333_);
lean_dec_ref(v_arg_2332_);
lean_dec(v_a_2322_);
lean_dec_ref(v_codomain_2295_);
lean_dec_ref(v_x_2294_);
v_a_2364_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2334_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2334_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2322_);
lean_dec_ref(v_codomain_2295_);
lean_dec_ref(v_x_2294_);
return v___x_2323_;
}
}
else
{
lean_dec_ref(v_codomain_2295_);
lean_dec_ref(v_x_2294_);
return v___x_2321_;
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec_ref(v_codomain_2295_);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = lean_array_get_borrowed(v___x_2312_, v_alts_2296_, v___x_2372_);
v___x_2374_ = lean_mk_empty_array_with_capacity(v___x_2319_);
v___x_2375_ = lean_array_push(v___x_2374_, v_x_2294_);
lean_inc(v___x_2373_);
v___x_2376_ = l_Lean_Expr_beta(v___x_2373_, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object* v_ctor_2391_, lean_object* v___x_2392_, lean_object* v_arg_2393_, lean_object* v_arg_2394_, lean_object* v___x_2395_, lean_object* v_a_2396_, lean_object* v_alts_2397_, uint8_t v___x_2398_, uint8_t v___x_2399_, uint8_t v___x_2400_, lean_object* v_y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2407_ = l_Lean_Expr_const___override(v_ctor_2391_, v___x_2392_);
lean_inc_ref_n(v_y_2401_, 2);
v___x_2408_ = l_Lean_mkApp3(v___x_2407_, v_arg_2393_, v_arg_2394_, v_y_2401_);
lean_inc_ref(v___x_2395_);
v___x_2409_ = lean_array_push(v___x_2395_, v___x_2408_);
v___x_2410_ = l_Lean_Expr_beta(v_a_2396_, v___x_2409_);
v___x_2411_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_y_2401_, v___x_2410_, v_alts_2397_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v___x_2413_ = lean_array_push(v___x_2395_, v_y_2401_);
v___x_2414_ = l_Lean_Meta_mkLambdaFVars(v___x_2413_, v_a_2412_, v___x_2398_, v___x_2399_, v___x_2398_, v___x_2399_, v___x_2400_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec_ref(v___x_2413_);
return v___x_2414_;
}
else
{
lean_dec_ref(v_y_2401_);
lean_dec_ref(v___x_2395_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1___boxed(lean_object** _args){
lean_object* v___x_2415_ = _args[0];
lean_object* v___x_2416_ = _args[1];
lean_object* v_arg_2417_ = _args[2];
lean_object* v_arg_2418_ = _args[3];
lean_object* v___x_2419_ = _args[4];
lean_object* v_a_2420_ = _args[5];
lean_object* v___x_2421_ = _args[6];
lean_object* v___x_2422_ = _args[7];
lean_object* v___x_2423_ = _args[8];
lean_object* v___x_2424_ = _args[9];
lean_object* v_ctor_2425_ = _args[10];
lean_object* v_d_2426_ = _args[11];
lean_object* v_alts_2427_ = _args[12];
lean_object* v___y_2428_ = _args[13];
lean_object* v___y_2429_ = _args[14];
lean_object* v___y_2430_ = _args[15];
lean_object* v___y_2431_ = _args[16];
lean_object* v___y_2432_ = _args[17];
_start:
{
uint8_t v___x_2353__boxed_2433_; uint8_t v___x_2354__boxed_2434_; uint8_t v___x_2355__boxed_2435_; lean_object* v_res_2436_; 
v___x_2353__boxed_2433_ = lean_unbox(v___x_2421_);
v___x_2354__boxed_2434_ = lean_unbox(v___x_2422_);
v___x_2355__boxed_2435_ = lean_unbox(v___x_2423_);
v_res_2436_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(v___x_2415_, v___x_2416_, v_arg_2417_, v_arg_2418_, v___x_2419_, v_a_2420_, v___x_2353__boxed_2433_, v___x_2354__boxed_2434_, v___x_2355__boxed_2435_, v___x_2424_, v_ctor_2425_, v_d_2426_, v_alts_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec_ref(v___x_2424_);
lean_dec(v___x_2415_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object* v_x_2437_, lean_object* v_codomain_2438_, lean_object* v_alts_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2437_, v_codomain_2438_, v_alts_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec_ref(v_alts_2439_);
return v_res_2445_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2447_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2448_ = lean_unsigned_to_nat(21u);
v___x_2449_ = lean_unsigned_to_nat(432u);
v___x_2450_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0));
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2452_ = l_mkPanicMessageWithDecl(v___x_2451_, v___x_2450_, v___x_2449_, v___x_2448_, v___x_2447_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object* v___x_2453_, lean_object* v_es_2454_, lean_object* v_xs_2455_, lean_object* v_codomain_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = lean_array_get_size(v_xs_2455_);
v___x_2463_ = lean_nat_dec_eq(v___x_2462_, v___x_2453_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
lean_dec_ref(v_codomain_2456_);
v___x_2464_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1);
v___x_2465_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2464_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
return v___x_2465_;
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = lean_array_fget_borrowed(v_xs_2455_, v___x_2466_);
lean_inc(v___x_2467_);
v___x_2468_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2467_, v_codomain_2456_, v_es_2454_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = lean_mk_empty_array_with_capacity(v___x_2453_);
lean_inc(v___x_2467_);
v___x_2471_ = lean_array_push(v___x_2470_, v___x_2467_);
v___x_2472_ = 0;
v___x_2473_ = 1;
v___x_2474_ = l_Lean_Meta_mkLambdaFVars(v___x_2471_, v_a_2469_, v___x_2472_, v___x_2463_, v___x_2472_, v___x_2463_, v___x_2473_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec_ref(v___x_2471_);
return v___x_2474_;
}
else
{
return v___x_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed(lean_object* v___x_2475_, lean_object* v_es_2476_, lean_object* v_xs_2477_, lean_object* v_codomain_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(v___x_2475_, v_es_2476_, v_xs_2477_, v_codomain_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_xs_2477_);
lean_dec_ref(v_es_2476_);
lean_dec(v___x_2475_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(lean_object* v_resultType_2485_, lean_object* v_es_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; lean_object* v___f_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2492_ = lean_unsigned_to_nat(1u);
v___f_2493_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2493_, 0, v___x_2492_);
lean_closure_set(v___f_2493_, 1, v_es_2486_);
v___x_2494_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2495_ = 0;
v___x_2496_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_resultType_2485_, v___x_2494_, v___f_2493_, v___x_2495_, v___x_2495_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___boxed(lean_object* v_resultType_2497_, lean_object* v_es_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_2497_, v_es_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(size_t v_sz_2505_, size_t v_i_2506_, lean_object* v_bs_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
uint8_t v___x_2513_; 
v___x_2513_ = lean_usize_dec_lt(v_i_2506_, v_sz_2505_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_bs_2507_);
return v___x_2514_;
}
else
{
lean_object* v_v_2515_; lean_object* v___x_2516_; lean_object* v_bs_x27_2517_; lean_object* v___x_2518_; 
v_v_2515_ = lean_array_uget(v_bs_2507_, v_i_2506_);
v___x_2516_ = lean_unsigned_to_nat(0u);
v_bs_x27_2517_ = lean_array_uset(v_bs_2507_, v_i_2506_, v___x_2516_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
v___x_2518_ = lean_infer_type(v_v_2515_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; size_t v___x_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2520_ = ((size_t)1ULL);
v___x_2521_ = lean_usize_add(v_i_2506_, v___x_2520_);
v___x_2522_ = lean_array_uset(v_bs_x27_2517_, v_i_2506_, v_a_2519_);
v_i_2506_ = v___x_2521_;
v_bs_2507_ = v___x_2522_;
goto _start;
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v_bs_x27_2517_);
v_a_2524_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2518_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2518_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0___boxed(lean_object* v_sz_2532_, lean_object* v_i_2533_, lean_object* v_bs_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
size_t v_sz_boxed_2540_; size_t v_i_boxed_2541_; lean_object* v_res_2542_; 
v_sz_boxed_2540_ = lean_unbox_usize(v_sz_2532_);
lean_dec(v_sz_2532_);
v_i_boxed_2541_ = lean_unbox_usize(v_i_2533_);
lean_dec(v_i_2533_);
v_res_2542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_boxed_2540_, v_i_boxed_2541_, v_bs_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry(lean_object* v_es_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
size_t v_sz_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v_sz_2549_ = lean_array_size(v_es_2543_);
v___x_2550_ = ((size_t)0ULL);
lean_inc_ref(v_es_2543_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2549_, v___x_2550_, v_es_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v___x_2553_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2552_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2555_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v___x_2555_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_a_2554_, v_es_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
return v___x_2555_;
}
else
{
lean_dec_ref(v_es_2543_);
return v___x_2553_;
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v_es_2543_);
v_a_2556_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2551_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2551_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurry___boxed(lean_object* v_es_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_es_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
return v_res_2570_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2572_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2573_ = lean_unsigned_to_nat(21u);
v___x_2574_ = lean_unsigned_to_nat(452u);
v___x_2575_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__0));
v___x_2576_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2577_ = l_mkPanicMessageWithDecl(v___x_2576_, v___x_2575_, v___x_2574_, v___x_2573_, v___x_2572_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(lean_object* v___x_2578_, lean_object* v_es_2579_, lean_object* v_xs_2580_, lean_object* v_codomain_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2587_ = lean_array_get_size(v_xs_2580_);
v___x_2588_ = lean_nat_dec_eq(v___x_2587_, v___x_2578_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec_ref(v_codomain_2581_);
v___x_2589_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1);
v___x_2590_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2589_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
return v___x_2590_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = lean_array_fget_borrowed(v_xs_2580_, v___x_2591_);
lean_inc(v___x_2592_);
v___x_2593_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2592_, v_codomain_2581_, v_es_2579_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = lean_mk_empty_array_with_capacity(v___x_2578_);
lean_inc(v___x_2592_);
v___x_2596_ = lean_array_push(v___x_2595_, v___x_2592_);
v___x_2597_ = 0;
v___x_2598_ = 1;
v___x_2599_ = l_Lean_Meta_mkLambdaFVars(v___x_2596_, v_a_2594_, v___x_2597_, v___x_2588_, v___x_2597_, v___x_2588_, v___x_2598_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec_ref(v___x_2596_);
return v___x_2599_;
}
else
{
return v___x_2593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object* v___x_2600_, lean_object* v_es_2601_, lean_object* v_xs_2602_, lean_object* v_codomain_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2600_, v_es_2601_, v_xs_2602_, v_codomain_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_xs_2602_);
lean_dec_ref(v_es_2601_);
lean_dec(v___x_2600_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object* v_es_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
size_t v_sz_2616_; size_t v___x_2617_; lean_object* v___x_2618_; 
v_sz_2616_ = lean_array_size(v_es_2610_);
v___x_2617_ = ((size_t)0ULL);
lean_inc_ref(v_es_2610_);
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2616_, v___x_2617_, v_es_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_a_2619_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2622_; lean_object* v___f_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; lean_object* v___x_2626_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = lean_unsigned_to_nat(1u);
v___f_2623_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2623_, 0, v___x_2622_);
lean_closure_set(v___f_2623_, 1, v_es_2610_);
v___x_2624_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2625_ = 0;
v___x_2626_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_2621_, v___x_2624_, v___f_2623_, v___x_2625_, v___x_2625_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
return v___x_2626_;
}
else
{
lean_dec_ref(v_es_2610_);
return v___x_2620_;
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v_es_2610_);
v_a_2627_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2618_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2618_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object* v_es_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object* v_a_2642_, lean_object* v_domain_2643_, lean_object* v___x_2644_, lean_object* v_type_2645_, uint8_t v___x_2646_, lean_object* v_x_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = l_List_lengthTR___redArg(v_a_2642_);
lean_inc_ref(v_x_2647_);
v___x_2654_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2653_, v_domain_2643_, v___x_2644_, v_x_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___x_2653_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v___x_2656_ = lean_unsigned_to_nat(1u);
v___x_2657_ = lean_mk_empty_array_with_capacity(v___x_2656_);
lean_inc_ref(v___x_2657_);
v___x_2658_ = lean_array_push(v___x_2657_, v_a_2655_);
v___x_2659_ = l_Lean_Meta_instantiateForall(v_type_2645_, v___x_2658_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec_ref(v___x_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; uint8_t v___x_2663_; lean_object* v___x_2664_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = lean_array_push(v___x_2657_, v_x_2647_);
v___x_2662_ = 0;
v___x_2663_ = 1;
v___x_2664_ = l_Lean_Meta_mkForallFVars(v___x_2661_, v_a_2660_, v___x_2662_, v___x_2646_, v___x_2646_, v___x_2663_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec_ref(v___x_2661_);
return v___x_2664_;
}
else
{
lean_dec_ref(v___x_2657_);
lean_dec_ref(v_x_2647_);
return v___x_2659_;
}
}
else
{
lean_dec_ref(v_x_2647_);
lean_dec_ref(v_type_2645_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object* v_a_2665_, lean_object* v_domain_2666_, lean_object* v___x_2667_, lean_object* v_type_2668_, lean_object* v___x_2669_, lean_object* v_x_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
uint8_t v___x_791__boxed_2676_; lean_object* v_res_2677_; 
v___x_791__boxed_2676_ = lean_unbox(v___x_2669_);
v_res_2677_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2665_, v_domain_2666_, v___x_2667_, v_type_2668_, v___x_791__boxed_2676_, v_x_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___x_2667_);
lean_dec(v_a_2665_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object* v_a_2678_, lean_object* v_domain_2679_, lean_object* v_type_2680_, size_t v_sz_2681_, size_t v_i_2682_, lean_object* v_bs_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v___x_2689_; 
v___x_2689_ = lean_usize_dec_lt(v_i_2682_, v_sz_2681_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; 
lean_dec_ref(v_type_2680_);
lean_dec_ref(v_domain_2679_);
lean_dec(v_a_2678_);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_bs_2683_);
return v___x_2690_;
}
else
{
lean_object* v_v_2691_; lean_object* v___x_2692_; lean_object* v_bs_x27_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_v_2691_ = lean_array_uget(v_bs_2683_, v_i_2682_);
v___x_2692_ = lean_unsigned_to_nat(0u);
v_bs_x27_2693_ = lean_array_uset(v_bs_2683_, v_i_2682_, v___x_2692_);
v___x_2694_ = lean_usize_to_nat(v_i_2682_);
v___x_2695_ = lean_box(v___x_2689_);
lean_inc_ref(v_type_2680_);
lean_inc_ref(v_domain_2679_);
lean_inc(v_a_2678_);
v___f_2696_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2696_, 0, v_a_2678_);
lean_closure_set(v___f_2696_, 1, v_domain_2679_);
lean_closure_set(v___f_2696_, 2, v___x_2694_);
lean_closure_set(v___f_2696_, 3, v_type_2680_);
lean_closure_set(v___f_2696_, 4, v___x_2695_);
v___x_2697_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2698_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_2697_, v_v_2691_, v___f_2696_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; size_t v___x_2700_; size_t v___x_2701_; lean_object* v___x_2702_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = ((size_t)1ULL);
v___x_2701_ = lean_usize_add(v_i_2682_, v___x_2700_);
v___x_2702_ = lean_array_uset(v_bs_x27_2693_, v_i_2682_, v_a_2699_);
v_i_2682_ = v___x_2701_;
v_bs_2683_ = v___x_2702_;
goto _start;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_bs_x27_2693_);
lean_dec_ref(v_type_2680_);
lean_dec_ref(v_domain_2679_);
lean_dec(v_a_2678_);
v_a_2704_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2698_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2698_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object* v_a_2712_, lean_object* v_domain_2713_, lean_object* v_type_2714_, lean_object* v_sz_2715_, lean_object* v_i_2716_, lean_object* v_bs_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
size_t v_sz_boxed_2723_; size_t v_i_boxed_2724_; lean_object* v_res_2725_; 
v_sz_boxed_2723_ = lean_unbox_usize(v_sz_2715_);
lean_dec(v_sz_2715_);
v_i_boxed_2724_ = lean_unbox_usize(v_i_2716_);
lean_dec(v_i_2716_);
v_res_2725_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2712_, v_domain_2713_, v_type_2714_, v_sz_boxed_2723_, v_i_boxed_2724_, v_bs_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object* v_n_2726_, lean_object* v_type_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; uint8_t v___x_2753_; 
v___x_2753_ = l_Lean_Expr_isForall(v_type_2727_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
v___x_2754_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_2755_ = l_Lean_MessageData_ofExpr(v_type_2727_);
v___x_2756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2756_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
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
else
{
v___y_2734_ = v_a_2728_;
v___y_2735_ = v_a_2729_;
v___y_2736_ = v_a_2730_;
v___y_2737_ = v_a_2731_;
goto v___jp_2733_;
}
v___jp_2733_:
{
lean_object* v_domain_2738_; lean_object* v___x_2739_; 
v_domain_2738_ = l_Lean_Expr_bindingDomain_x21(v_type_2727_);
lean_inc_ref(v_domain_2738_);
v___x_2739_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_2726_, v_domain_2738_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2741_; size_t v_sz_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc_n(v_a_2740_, 2);
lean_dec_ref_known(v___x_2739_, 1);
v___x_2741_ = lean_array_mk(v_a_2740_);
v_sz_2742_ = lean_array_size(v___x_2741_);
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2740_, v_domain_2738_, v_type_2727_, v_sz_2742_, v___x_2743_, v___x_2741_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2744_;
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v_domain_2738_);
lean_dec_ref(v_type_2727_);
v_a_2745_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2739_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2739_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object* v_n_2766_, lean_object* v_type_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2766_, v_type_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_n_2766_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object* v_a_2774_, lean_object* v_domain_2775_, lean_object* v_type_2776_, lean_object* v_as_2777_, size_t v_sz_2778_, size_t v_i_2779_, lean_object* v_bs_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2774_, v_domain_2775_, v_type_2776_, v_sz_2778_, v_i_2779_, v_bs_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object* v_a_2787_, lean_object* v_domain_2788_, lean_object* v_type_2789_, lean_object* v_as_2790_, lean_object* v_sz_2791_, lean_object* v_i_2792_, lean_object* v_bs_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
size_t v_sz_boxed_2799_; size_t v_i_boxed_2800_; lean_object* v_res_2801_; 
v_sz_boxed_2799_ = lean_unbox_usize(v_sz_2791_);
lean_dec(v_sz_2791_);
v_i_boxed_2800_ = lean_unbox_usize(v_i_2792_);
lean_dec(v_i_2792_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2787_, v_domain_2788_, v_type_2789_, v_as_2790_, v_sz_boxed_2799_, v_i_boxed_2800_, v_bs_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v_as_2790_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object* v_argsPacker_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_array_get_size(v_argsPacker_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object* v_argsPacker_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_2804_);
lean_dec_ref(v_argsPacker_2804_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t v_sz_2806_, size_t v_i_2807_, lean_object* v_bs_2808_){
_start:
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_usize_dec_lt(v_i_2807_, v_sz_2806_);
if (v___x_2809_ == 0)
{
return v_bs_2808_;
}
else
{
lean_object* v_v_2810_; lean_object* v___x_2811_; lean_object* v_bs_x27_2812_; lean_object* v___x_2813_; size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v_v_2810_ = lean_array_uget(v_bs_2808_, v_i_2807_);
v___x_2811_ = lean_unsigned_to_nat(0u);
v_bs_x27_2812_ = lean_array_uset(v_bs_2808_, v_i_2807_, v___x_2811_);
v___x_2813_ = lean_array_get_size(v_v_2810_);
lean_dec(v_v_2810_);
v___x_2814_ = ((size_t)1ULL);
v___x_2815_ = lean_usize_add(v_i_2807_, v___x_2814_);
v___x_2816_ = lean_array_uset(v_bs_x27_2812_, v_i_2807_, v___x_2813_);
v_i_2807_ = v___x_2815_;
v_bs_2808_ = v___x_2816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object* v_sz_2818_, lean_object* v_i_2819_, lean_object* v_bs_2820_){
_start:
{
size_t v_sz_boxed_2821_; size_t v_i_boxed_2822_; lean_object* v_res_2823_; 
v_sz_boxed_2821_ = lean_unbox_usize(v_sz_2818_);
lean_dec(v_sz_2818_);
v_i_boxed_2822_ = lean_unbox_usize(v_i_2819_);
lean_dec(v_i_2819_);
v_res_2823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_2821_, v_i_boxed_2822_, v_bs_2820_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object* v_argsPacker_2824_){
_start:
{
size_t v_sz_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v_sz_2825_ = lean_array_size(v_argsPacker_2824_);
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2825_, v___x_2826_, v_argsPacker_2824_);
return v___x_2827_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0(void){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Array_instInhabited___redArg();
return v___x_2828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object* v_argsPacker_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2830_ = lean_array_get_size(v_argsPacker_2829_);
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = lean_nat_dec_eq(v___x_2830_, v___x_2831_);
if (v___x_2832_ == 0)
{
return v___x_2832_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2833_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2834_ = lean_unsigned_to_nat(0u);
v___x_2835_ = lean_array_get_borrowed(v___x_2833_, v_argsPacker_2829_, v___x_2834_);
v___x_2836_ = lean_array_get_size(v___x_2835_);
v___x_2837_ = lean_nat_dec_eq(v___x_2836_, v___x_2831_);
return v___x_2837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object* v_argsPacker_2838_){
_start:
{
uint8_t v_res_2839_; lean_object* v_r_2840_; 
v_res_2839_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2838_);
lean_dec_ref(v_argsPacker_2838_);
v_r_2840_ = lean_box(v_res_2839_);
return v_r_2840_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__2(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2843_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__1));
v___x_2844_ = lean_unsigned_to_nat(2u);
v___x_2845_ = lean_unsigned_to_nat(487u);
v___x_2846_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2847_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2848_ = l_mkPanicMessageWithDecl(v___x_2847_, v___x_2846_, v___x_2845_, v___x_2844_, v___x_2843_);
return v___x_2848_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__4(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2850_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__3));
v___x_2851_ = lean_unsigned_to_nat(2u);
v___x_2852_ = lean_unsigned_to_nat(488u);
v___x_2853_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2854_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2855_ = l_mkPanicMessageWithDecl(v___x_2854_, v___x_2853_, v___x_2852_, v___x_2851_, v___x_2850_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object* v_argsPacker_2856_, lean_object* v_domain_2857_, lean_object* v_fidx_2858_, lean_object* v_args_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = lean_array_get_size(v_argsPacker_2856_);
v___x_2866_ = lean_nat_dec_lt(v_fidx_2858_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec(v_fidx_2858_);
lean_dec_ref(v_domain_2857_);
v___x_2867_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__2, &l_Lean_Meta_ArgsPacker_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__2);
v___x_2868_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2867_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
return v___x_2868_;
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2869_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2870_ = lean_array_get_size(v_args_2859_);
v___x_2871_ = lean_array_get_borrowed(v___x_2869_, v_argsPacker_2856_, v_fidx_2858_);
v___x_2872_ = lean_array_get_size(v___x_2871_);
v___x_2873_ = lean_nat_dec_eq(v___x_2870_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_dec(v_fidx_2858_);
lean_dec_ref(v_domain_2857_);
v___x_2874_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__4, &l_Lean_Meta_ArgsPacker_pack___closed__4_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__4);
v___x_2875_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2874_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_domain_2857_);
v___x_2877_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_2865_, v_domain_2857_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
lean_inc(v_fidx_2858_);
v___x_2879_ = l_List_get_x21Internal___redArg(v___x_2876_, v_a_2878_, v_fidx_2858_);
lean_dec(v_a_2878_);
v___x_2880_ = l_Lean_Meta_ArgsPacker_Unary_pack(v___x_2879_, v_args_2859_);
lean_dec(v___x_2879_);
v___x_2881_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2865_, v_domain_2857_, v_fidx_2858_, v___x_2880_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
lean_dec(v_fidx_2858_);
return v___x_2881_;
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_fidx_2858_);
lean_dec_ref(v_domain_2857_);
v_a_2882_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2877_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2877_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object* v_argsPacker_2890_, lean_object* v_domain_2891_, lean_object* v_fidx_2892_, lean_object* v_args_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2890_, v_domain_2891_, v_fidx_2892_, v_args_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec_ref(v_args_2893_);
lean_dec_ref(v_argsPacker_2890_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object* v_argsPacker_2900_, lean_object* v_e_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_array_get_size(v_argsPacker_2900_);
v___x_2903_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_2902_, v_e_2901_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_box(0);
return v___x_2904_;
}
else
{
lean_object* v_val_2905_; lean_object* v_fst_2906_; lean_object* v_snd_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2927_; 
v_val_2905_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_val_2905_);
lean_dec_ref_known(v___x_2903_, 1);
v_fst_2906_ = lean_ctor_get(v_val_2905_, 0);
v_snd_2907_ = lean_ctor_get(v_val_2905_, 1);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_val_2905_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2909_ = v_val_2905_;
v_isShared_2910_ = v_isSharedCheck_2927_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_snd_2907_);
lean_inc(v_fst_2906_);
lean_dec(v_val_2905_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2927_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2911_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2912_ = lean_array_get_borrowed(v___x_2911_, v_argsPacker_2900_, v_fst_2906_);
v___x_2913_ = lean_array_get_size(v___x_2912_);
v___x_2914_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_2913_, v_snd_2907_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v___x_2915_; 
lean_del_object(v___x_2909_);
lean_dec(v_fst_2906_);
v___x_2915_ = lean_box(0);
return v___x_2915_;
}
else
{
lean_object* v_val_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2926_; 
v_val_2916_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2918_ = v___x_2914_;
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_val_2916_);
lean_dec(v___x_2914_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2926_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v_val_2916_);
v___x_2921_ = v___x_2909_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_fst_2906_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_val_2916_);
v___x_2921_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2923_; 
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2921_);
v___x_2923_ = v___x_2918_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object* v_argsPacker_2928_, lean_object* v_e_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_2928_, v_e_2929_);
lean_dec_ref(v_argsPacker_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object* v_as_2931_, lean_object* v_bs_2932_, lean_object* v_i_2933_, lean_object* v_cs_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_as_2931_);
v___x_2941_ = lean_nat_dec_lt(v_i_2933_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec(v_i_2933_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_cs_2934_);
return v___x_2942_;
}
else
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = lean_array_get_size(v_bs_2932_);
v___x_2944_ = lean_nat_dec_lt(v_i_2933_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; 
lean_dec(v_i_2933_);
v___x_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2945_, 0, v_cs_2934_);
return v___x_2945_;
}
else
{
lean_object* v_a_2946_; lean_object* v_b_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_array_fget_borrowed(v_as_2931_, v_i_2933_);
v_b_2947_ = lean_array_fget_borrowed(v_bs_2932_, v_i_2933_);
lean_inc(v_b_2947_);
lean_inc(v_a_2946_);
v___x_2948_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_a_2946_, v_b_2947_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = lean_unsigned_to_nat(1u);
v___x_2951_ = lean_nat_add(v_i_2933_, v___x_2950_);
lean_dec(v_i_2933_);
v___x_2952_ = lean_array_push(v_cs_2934_, v_a_2949_);
v_i_2933_ = v___x_2951_;
v_cs_2934_ = v___x_2952_;
goto _start;
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v_cs_2934_);
lean_dec(v_i_2933_);
v_a_2954_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2948_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2948_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object* v_as_2962_, lean_object* v_bs_2963_, lean_object* v_i_2964_, lean_object* v_cs_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_2962_, v_bs_2963_, v_i_2964_, v_cs_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v_bs_2963_);
lean_dec_ref(v_as_2962_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object* v_argsPacker_2972_, lean_object* v_types_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_2981_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_argsPacker_2972_, v_types_2973_, v___x_2979_, v___x_2980_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
v___x_2983_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2982_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
return v___x_2983_;
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
v_a_2984_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2981_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2981_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object* v_argsPacker_2992_, lean_object* v_types_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2992_, v_types_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec_ref(v_types_2993_);
lean_dec_ref(v_argsPacker_2992_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object* v_as_3000_, lean_object* v_bs_3001_, lean_object* v_i_3002_, lean_object* v_cs_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = lean_array_get_size(v_as_3000_);
v___x_3010_ = lean_nat_dec_lt(v_i_3002_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; 
lean_dec(v_i_3002_);
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_cs_3003_);
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3012_ = lean_array_get_size(v_bs_3001_);
v___x_3013_ = lean_nat_dec_lt(v_i_3002_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_i_3002_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v_cs_3003_);
return v___x_3014_;
}
else
{
lean_object* v_a_3015_; lean_object* v_b_3016_; lean_object* v___x_3017_; 
v_a_3015_ = lean_array_fget_borrowed(v_as_3000_, v_i_3002_);
v_b_3016_ = lean_array_fget_borrowed(v_bs_3001_, v_i_3002_);
lean_inc(v_b_3016_);
lean_inc(v_a_3015_);
v___x_3017_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_a_3015_, v_b_3016_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = lean_unsigned_to_nat(1u);
v___x_3020_ = lean_nat_add(v_i_3002_, v___x_3019_);
lean_dec(v_i_3002_);
v___x_3021_ = lean_array_push(v_cs_3003_, v_a_3018_);
v_i_3002_ = v___x_3020_;
v_cs_3003_ = v___x_3021_;
goto _start;
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v_cs_3003_);
lean_dec(v_i_3002_);
v_a_3023_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3017_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3017_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object* v_as_3031_, lean_object* v_bs_3032_, lean_object* v_i_3033_, lean_object* v_cs_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3031_, v_bs_3032_, v_i_3033_, v_cs_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v_bs_3032_);
lean_dec_ref(v_as_3031_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object* v_argsPacker_3041_, lean_object* v_es_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = lean_unsigned_to_nat(0u);
v___x_3049_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3050_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3041_, v_es_3042_, v___x_3048_, v___x_3049_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_a_3051_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
return v___x_3052_;
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3053_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3050_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3050_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object* v_argsPacker_3061_, lean_object* v_es_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3061_, v_es_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec_ref(v_es_3062_);
lean_dec_ref(v_argsPacker_3061_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object* v_argsPacker_3069_, lean_object* v_resultType_3070_, lean_object* v_es_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = lean_unsigned_to_nat(0u);
v___x_3078_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3079_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3069_, v_es_3071_, v___x_3077_, v___x_3078_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3081_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_3070_, v_a_3080_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3081_;
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec_ref(v_resultType_3070_);
v_a_3082_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3079_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3079_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object* v_argsPacker_3090_, lean_object* v_resultType_3091_, lean_object* v_es_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3090_, v_resultType_3091_, v_es_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec_ref(v_es_3092_);
lean_dec_ref(v_argsPacker_3090_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object* v_argsPacker_3099_, lean_object* v_es_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_unsigned_to_nat(0u);
v___x_3107_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3108_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3099_, v_es_3100_, v___x_3106_, v___x_3107_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_a_3109_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
return v___x_3110_;
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
v_a_3111_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3108_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3108_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object* v_argsPacker_3119_, lean_object* v_es_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3119_, v_es_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec_ref(v_es_3120_);
lean_dec_ref(v_argsPacker_3119_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object* v_msg_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___f_3133_; lean_object* v___x_920__overap_3134_; lean_object* v___x_3135_; 
v___f_3133_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_920__overap_3134_ = lean_panic_fn_borrowed(v___f_3133_, v_msg_3127_);
lean_inc(v___y_3131_);
lean_inc_ref(v___y_3130_);
lean_inc(v___y_3129_);
lean_inc_ref(v___y_3128_);
v___x_3135_ = lean_apply_5(v___x_920__overap_3134_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, lean_box(0));
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object* v_msg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object* v_a_3143_, lean_object* v___x_3144_, lean_object* v_i_3145_, lean_object* v_e_3146_, lean_object* v_x_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = l_List_lengthTR___redArg(v_a_3143_);
lean_inc_ref(v_x_3147_);
v___x_3154_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_3153_, v___x_3144_, v_i_3145_, v_x_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___x_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; uint8_t v___x_3162_; uint8_t v___x_3163_; lean_object* v___x_3164_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = lean_unsigned_to_nat(1u);
v___x_3157_ = lean_mk_empty_array_with_capacity(v___x_3156_);
lean_inc_ref(v___x_3157_);
v___x_3158_ = lean_array_push(v___x_3157_, v_x_3147_);
v___x_3159_ = lean_array_push(v___x_3157_, v_a_3155_);
v___x_3160_ = l_Lean_Expr_beta(v_e_3146_, v___x_3159_);
v___x_3161_ = 0;
v___x_3162_ = 1;
v___x_3163_ = 1;
v___x_3164_ = l_Lean_Meta_mkLambdaFVars(v___x_3158_, v___x_3160_, v___x_3161_, v___x_3162_, v___x_3161_, v___x_3162_, v___x_3163_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec_ref(v___x_3158_);
return v___x_3164_;
}
else
{
lean_dec_ref(v_x_3147_);
lean_dec_ref(v_e_3146_);
return v___x_3154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object* v_a_3165_, lean_object* v___x_3166_, lean_object* v_i_3167_, lean_object* v_e_3168_, lean_object* v_x_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3165_, v___x_3166_, v_i_3167_, v_e_3168_, v_x_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v_i_3167_);
lean_dec(v_a_3165_);
return v_res_3175_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__0));
v___x_3178_ = l_Lean_stringToMessageData(v___x_3177_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3181_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__3));
v___x_3182_ = lean_unsigned_to_nat(4u);
v___x_3183_ = lean_unsigned_to_nat(553u);
v___x_3184_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__2));
v___x_3185_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_3186_ = l_mkPanicMessageWithDecl(v___x_3185_, v___x_3184_, v___x_3183_, v___x_3182_, v___x_3181_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object* v_argsPacker_3187_, lean_object* v_e_3188_, lean_object* v_i_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v_n_3197_; lean_object* v___x_3198_; 
v___x_3195_ = l_Lean_instInhabitedExpr;
v___x_3196_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v_n_3197_ = lean_array_get_size(v_argsPacker_3187_);
lean_inc(v_a_3193_);
lean_inc_ref(v_a_3192_);
lean_inc(v_a_3191_);
lean_inc_ref(v_a_3190_);
lean_inc_ref(v_e_3188_);
v___x_3198_ = lean_infer_type(v_e_3188_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3200_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3198_, 1);
lean_inc(v_a_3193_);
lean_inc_ref(v_a_3192_);
lean_inc(v_a_3191_);
lean_inc_ref(v_a_3190_);
v___x_3200_ = lean_whnf(v_a_3199_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v___x_3244_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v___x_3244_ = l_Lean_Expr_isForall(v_a_3201_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__4, &l_Lean_Meta_ArgsPacker_curryProj___closed__4_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4);
v___x_3246_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v___x_3245_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_dec_ref_known(v___x_3246_, 1);
v___y_3216_ = v_a_3190_;
v___y_3217_ = v_a_3191_;
v___y_3218_ = v_a_3192_;
v___y_3219_ = v_a_3193_;
goto v___jp_3215_;
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec(v_a_3201_);
lean_dec(v_i_3189_);
lean_dec_ref(v_e_3188_);
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
else
{
v___y_3216_ = v_a_3190_;
v___y_3217_ = v_a_3191_;
v___y_3218_ = v_a_3192_;
v___y_3219_ = v_a_3193_;
goto v___jp_3215_;
}
v___jp_3202_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_inc(v_i_3189_);
v___x_3209_ = l_List_get_x21Internal___redArg(v___x_3195_, v___y_3203_, v_i_3189_);
lean_dec(v___y_3203_);
v___x_3210_ = l_Lean_Expr_bindingName_x21(v_a_3201_);
lean_dec(v_a_3201_);
v___x_3211_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3210_, v___x_3209_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = lean_array_get_borrowed(v___x_3196_, v_argsPacker_3187_, v_i_3189_);
lean_dec(v_i_3189_);
lean_inc(v___x_3213_);
v___x_3214_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v___x_3213_, v_a_3212_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
return v___x_3214_;
}
else
{
lean_dec(v_i_3189_);
return v___x_3211_;
}
}
v___jp_3215_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = l_Lean_Expr_bindingDomain_x21(v_a_3201_);
lean_inc_ref(v___x_3220_);
v___x_3221_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_3197_, v___x_3220_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___f_3223_; lean_object* v___x_3224_; uint8_t v___x_3225_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc_n(v_a_3222_, 2);
lean_dec_ref_known(v___x_3221_, 1);
lean_inc(v_i_3189_);
v___f_3223_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3223_, 0, v_a_3222_);
lean_closure_set(v___f_3223_, 1, v___x_3220_);
lean_closure_set(v___f_3223_, 2, v_i_3189_);
lean_closure_set(v___f_3223_, 3, v_e_3188_);
v___x_3224_ = l_List_lengthTR___redArg(v_a_3222_);
v___x_3225_ = lean_nat_dec_lt(v_i_3189_, v___x_3224_);
lean_dec(v___x_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v___f_3223_);
lean_dec(v_a_3222_);
lean_dec(v_a_3201_);
lean_dec(v_i_3189_);
v___x_3226_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__1, &l_Lean_Meta_ArgsPacker_curryProj___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1);
v___x_3227_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3226_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
else
{
v___y_3203_ = v_a_3222_;
v___y_3204_ = v___f_3223_;
v___y_3205_ = v___y_3216_;
v___y_3206_ = v___y_3217_;
v___y_3207_ = v___y_3218_;
v___y_3208_ = v___y_3219_;
goto v___jp_3202_;
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v___x_3220_);
lean_dec(v_a_3201_);
lean_dec(v_i_3189_);
lean_dec_ref(v_e_3188_);
v_a_3236_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3221_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3221_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
else
{
lean_dec(v_i_3189_);
lean_dec_ref(v_e_3188_);
return v___x_3200_;
}
}
else
{
lean_dec(v_i_3189_);
lean_dec_ref(v_e_3188_);
return v___x_3198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object* v_argsPacker_3255_, lean_object* v_e_3256_, lean_object* v_i_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3255_, v_e_3256_, v_i_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec_ref(v_argsPacker_3255_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object* v_as_3264_, lean_object* v_bs_3265_, lean_object* v_i_3266_, lean_object* v_cs_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = lean_array_get_size(v_as_3264_);
v___x_3274_ = lean_nat_dec_lt(v_i_3266_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; 
lean_dec(v_i_3266_);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_cs_3267_);
return v___x_3275_;
}
else
{
lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = lean_array_get_size(v_bs_3265_);
v___x_3277_ = lean_nat_dec_lt(v_i_3266_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_dec(v_i_3266_);
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v_cs_3267_);
return v___x_3278_;
}
else
{
lean_object* v_a_3279_; lean_object* v_b_3280_; lean_object* v___x_3281_; 
v_a_3279_ = lean_array_fget_borrowed(v_as_3264_, v_i_3266_);
v_b_3280_ = lean_array_fget_borrowed(v_bs_3265_, v_i_3266_);
lean_inc(v_b_3280_);
lean_inc(v_a_3279_);
v___x_3281_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_3279_, v_b_3280_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v___x_3283_ = lean_unsigned_to_nat(1u);
v___x_3284_ = lean_nat_add(v_i_3266_, v___x_3283_);
lean_dec(v_i_3266_);
v___x_3285_ = lean_array_push(v_cs_3267_, v_a_3282_);
v_i_3266_ = v___x_3284_;
v_cs_3267_ = v___x_3285_;
goto _start;
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec_ref(v_cs_3267_);
lean_dec(v_i_3266_);
v_a_3287_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3281_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3281_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object* v_as_3295_, lean_object* v_bs_3296_, lean_object* v_i_3297_, lean_object* v_cs_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3295_, v_bs_3296_, v_i_3297_, v_cs_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec_ref(v_bs_3296_);
lean_dec_ref(v_as_3295_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object* v_argsPacker_3305_, lean_object* v_t_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_array_get_size(v_argsPacker_3305_);
v___x_3313_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v___x_3312_, v_t_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3313_, 1);
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3317_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_argsPacker_3305_, v_a_3314_, v___x_3315_, v___x_3316_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
lean_dec(v_a_3314_);
return v___x_3317_;
}
else
{
return v___x_3313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object* v_argsPacker_3318_, lean_object* v_t_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3318_, v_t_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec_ref(v_argsPacker_3318_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object* v_upperBound_3326_, lean_object* v_argsPacker_3327_, lean_object* v_e_3328_, lean_object* v_a_3329_, lean_object* v_b_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
uint8_t v___x_3336_; 
v___x_3336_ = lean_nat_dec_lt(v_a_3329_, v_upperBound_3326_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; 
lean_dec(v_a_3329_);
lean_dec_ref(v_e_3328_);
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_b_3330_);
return v___x_3337_;
}
else
{
lean_object* v___x_3338_; 
lean_inc(v_a_3329_);
lean_inc_ref(v_e_3328_);
v___x_3338_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3327_, v_e_3328_, v_a_3329_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = lean_array_push(v_b_3330_, v_a_3339_);
v___x_3341_ = lean_unsigned_to_nat(1u);
v___x_3342_ = lean_nat_add(v_a_3329_, v___x_3341_);
lean_dec(v_a_3329_);
v_a_3329_ = v___x_3342_;
v_b_3330_ = v___x_3340_;
goto _start;
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec_ref(v_b_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_e_3328_);
v_a_3344_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3338_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3338_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object* v_upperBound_3352_, lean_object* v_argsPacker_3353_, lean_object* v_e_3354_, lean_object* v_a_3355_, lean_object* v_b_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3352_, v_argsPacker_3353_, v_e_3354_, v_a_3355_, v_b_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec_ref(v_argsPacker_3353_);
lean_dec(v_upperBound_3352_);
return v_res_3362_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curry___closed__0(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = lean_unsigned_to_nat(0u);
v___x_3364_ = l_Lean_Level_ofNat(v___x_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object* v_argsPacker_3365_, lean_object* v_e_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v_es_3374_; lean_object* v___x_3375_; 
v___x_3372_ = lean_array_get_size(v_argsPacker_3365_);
v___x_3373_ = lean_unsigned_to_nat(0u);
v_es_3374_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3375_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_3372_, v_argsPacker_3365_, v_e_3366_, v___x_3373_, v_es_3374_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
v___x_3377_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curry___closed__0, &l_Lean_Meta_ArgsPacker_curry___closed__0_once, _init_l_Lean_Meta_ArgsPacker_curry___closed__0);
v___x_3378_ = l_Lean_Meta_PProdN_mk(v___x_3377_, v_a_3376_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
return v___x_3378_;
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v_a_3379_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3375_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3375_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object* v_argsPacker_3387_, lean_object* v_e_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3387_, v_e_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec_ref(v_argsPacker_3387_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object* v_upperBound_3395_, lean_object* v_argsPacker_3396_, lean_object* v_e_3397_, lean_object* v_inst_3398_, lean_object* v_R_3399_, lean_object* v_a_3400_, lean_object* v_b_3401_, lean_object* v_c_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3395_, v_argsPacker_3396_, v_e_3397_, v_a_3400_, v_b_3401_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object* v_upperBound_3409_, lean_object* v_argsPacker_3410_, lean_object* v_e_3411_, lean_object* v_inst_3412_, lean_object* v_R_3413_, lean_object* v_a_3414_, lean_object* v_b_3415_, lean_object* v_c_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3409_, v_argsPacker_3410_, v_e_3411_, v_inst_3412_, v_R_3413_, v_a_3414_, v_b_3415_, v_c_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v_argsPacker_3410_);
lean_dec(v_upperBound_3409_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object* v_a_3423_, lean_object* v_argsPacker_3424_, lean_object* v_name_3425_, lean_object* v_k_3426_, lean_object* v_tail_3427_, lean_object* v_x_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3423_, v_argsPacker_3424_, v_name_3425_, v_k_3426_, v_tail_3427_, v_x_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object* v_argsPacker_3435_, lean_object* v_name_3436_, lean_object* v_k_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
if (lean_obj_tag(v_a_3438_) == 0)
{
lean_object* v___x_3445_; 
lean_dec(v_name_3436_);
lean_dec_ref(v_argsPacker_3435_);
lean_inc(v_a_3443_);
lean_inc_ref(v_a_3442_);
lean_inc(v_a_3441_);
lean_inc_ref(v_a_3440_);
v___x_3445_ = lean_apply_6(v_k_3437_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, lean_box(0));
return v___x_3445_;
}
else
{
lean_object* v_head_3446_; lean_object* v_tail_3447_; lean_object* v___f_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v_head_3446_ = lean_ctor_get(v_a_3438_, 0);
lean_inc(v_head_3446_);
v_tail_3447_ = lean_ctor_get(v_a_3438_, 1);
lean_inc(v_tail_3447_);
lean_dec_ref_known(v_a_3438_, 2);
lean_inc(v_name_3436_);
lean_inc_ref(v_argsPacker_3435_);
lean_inc_ref(v_a_3439_);
v___f_3448_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3448_, 0, v_a_3439_);
lean_closure_set(v___f_3448_, 1, v_argsPacker_3435_);
lean_closure_set(v___f_3448_, 2, v_name_3436_);
lean_closure_set(v___f_3448_, 3, v_k_3437_);
lean_closure_set(v___f_3448_, 4, v_tail_3447_);
v___x_3449_ = lean_array_get_size(v_argsPacker_3435_);
lean_dec_ref(v_argsPacker_3435_);
v___x_3450_ = lean_unsigned_to_nat(1u);
v___x_3451_ = lean_nat_dec_eq(v___x_3449_, v___x_3450_);
if (v___x_3451_ == 0)
{
uint8_t v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3452_ = 1;
v___x_3453_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3436_, v___x_3452_);
v___x_3454_ = lean_array_get_size(v_a_3439_);
lean_dec_ref(v_a_3439_);
v___x_3455_ = lean_nat_add(v___x_3454_, v___x_3450_);
v___x_3456_ = l_Nat_reprFast(v___x_3455_);
v___x_3457_ = lean_string_append(v___x_3453_, v___x_3456_);
lean_dec_ref(v___x_3456_);
v___x_3458_ = lean_box(0);
v___x_3459_ = l_Lean_Name_str___override(v___x_3458_, v___x_3457_);
v___x_3460_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3459_, v_head_3446_, v___f_3448_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_3460_;
}
else
{
lean_object* v___x_3461_; 
lean_dec_ref(v_a_3439_);
v___x_3461_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_3436_, v_head_3446_, v___f_3448_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
return v___x_3461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object* v_a_3462_, lean_object* v_argsPacker_3463_, lean_object* v_name_3464_, lean_object* v_k_3465_, lean_object* v_tail_3466_, lean_object* v_x_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = lean_array_push(v_a_3462_, v_x_3467_);
v___x_3474_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3463_, v_name_3464_, v_k_3465_, v_tail_3466_, v___x_3473_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object* v_argsPacker_3475_, lean_object* v_name_3476_, lean_object* v_k_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3475_, v_name_3476_, v_k_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object* v_00_u03b1_3486_, lean_object* v_argsPacker_3487_, lean_object* v_name_3488_, lean_object* v_k_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3487_, v_name_3488_, v_k_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object* v_00_u03b1_3498_, lean_object* v_argsPacker_3499_, lean_object* v_name_3500_, lean_object* v_k_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(v_00_u03b1_3498_, v_argsPacker_3499_, v_name_3500_, v_k_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object* v_argsPacker_3510_, lean_object* v_name_3511_, lean_object* v_type_3512_, lean_object* v_k_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3510_, v_type_3512_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v___x_3521_ = lean_array_to_list(v_a_3520_);
v___x_3522_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3523_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3510_, v_name_3511_, v_k_3513_, v___x_3521_, v___x_3522_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_);
return v___x_3523_;
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec_ref(v_k_3513_);
lean_dec(v_name_3511_);
lean_dec_ref(v_argsPacker_3510_);
v_a_3524_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3519_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3519_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object* v_argsPacker_3532_, lean_object* v_name_3533_, lean_object* v_type_3534_, lean_object* v_k_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3532_, v_name_3533_, v_type_3534_, v_k_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object* v_00_u03b1_3542_, lean_object* v_argsPacker_3543_, lean_object* v_name_3544_, lean_object* v_type_3545_, lean_object* v_k_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3543_, v_name_3544_, v_type_3545_, v_k_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object* v_00_u03b1_3553_, lean_object* v_argsPacker_3554_, lean_object* v_name_3555_, lean_object* v_type_3556_, lean_object* v_k_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(v_00_u03b1_3553_, v_argsPacker_3554_, v_name_3555_, v_type_3556_, v_k_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object* v_argsPacker_3564_, lean_object* v_packedMotiveType_3565_, lean_object* v_type_3566_, lean_object* v_value_3567_, lean_object* v_k_3568_, lean_object* v_motives_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3564_, v_packedMotiveType_3565_, v_motives_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc_n(v_a_3576_, 2);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3577_ = lean_unsigned_to_nat(1u);
v___x_3578_ = lean_mk_empty_array_with_capacity(v___x_3577_);
v___x_3579_ = lean_array_push(v___x_3578_, v_a_3576_);
v___x_3580_ = l_Lean_Meta_instantiateForall(v_type_3566_, v___x_3579_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec_ref(v___x_3579_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
v___x_3582_ = l_Lean_Expr_app___override(v_value_3567_, v_a_3576_);
lean_inc(v___y_3573_);
lean_inc_ref(v___y_3572_);
lean_inc(v___y_3571_);
lean_inc_ref(v___y_3570_);
v___x_3583_ = lean_apply_8(v_k_3568_, v_motives_3569_, v___x_3582_, v_a_3581_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, lean_box(0));
return v___x_3583_;
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v_a_3576_);
lean_dec_ref(v_motives_3569_);
lean_dec_ref(v_k_3568_);
lean_dec_ref(v_value_3567_);
v_a_3584_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3580_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3580_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v_motives_3569_);
lean_dec_ref(v_k_3568_);
lean_dec_ref(v_value_3567_);
lean_dec_ref(v_type_3566_);
v_a_3592_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3575_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3575_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object* v_argsPacker_3600_, lean_object* v_packedMotiveType_3601_, lean_object* v_type_3602_, lean_object* v_value_3603_, lean_object* v_k_3604_, lean_object* v_motives_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3600_, v_packedMotiveType_3601_, v_type_3602_, v_value_3603_, v_k_3604_, v_motives_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_argsPacker_3600_);
return v_res_3611_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0));
v___x_3614_ = l_Lean_stringToMessageData(v___x_3613_);
return v___x_3614_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2));
v___x_3617_ = l_Lean_stringToMessageData(v___x_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object* v_argsPacker_3618_, lean_object* v_value_3619_, lean_object* v_type_3620_, lean_object* v_k_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; uint8_t v___x_3656_; 
v___x_3656_ = l_Lean_Expr_isForall(v_type_3620_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec_ref(v_k_3621_);
lean_dec_ref(v_value_3619_);
lean_dec_ref(v_argsPacker_3618_);
v___x_3657_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3);
v___x_3658_ = l_Lean_MessageData_ofExpr(v_type_3620_);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3659_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
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
v___y_3637_ = v_a_3622_;
v___y_3638_ = v_a_3623_;
v___y_3639_ = v_a_3624_;
v___y_3640_ = v_a_3625_;
goto v___jp_3636_;
}
v___jp_3627_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = l_Lean_Expr_bindingName_x21(v_type_3620_);
lean_dec_ref(v_type_3620_);
v___x_3635_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3618_, v___x_3634_, v___y_3629_, v___y_3628_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3635_;
}
v___jp_3636_:
{
lean_object* v_packedMotiveType_3641_; lean_object* v___f_3642_; uint8_t v___x_3643_; 
v_packedMotiveType_3641_ = l_Lean_Expr_bindingDomain_x21(v_type_3620_);
lean_inc_ref(v_type_3620_);
lean_inc_ref(v_packedMotiveType_3641_);
lean_inc_ref(v_argsPacker_3618_);
v___f_3642_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3642_, 0, v_argsPacker_3618_);
lean_closure_set(v___f_3642_, 1, v_packedMotiveType_3641_);
lean_closure_set(v___f_3642_, 2, v_type_3620_);
lean_closure_set(v___f_3642_, 3, v_value_3619_);
lean_closure_set(v___f_3642_, 4, v_k_3621_);
v___x_3643_ = l_Lean_Expr_isForall(v_packedMotiveType_3641_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec_ref(v___f_3642_);
lean_dec_ref(v_type_3620_);
lean_dec_ref(v_argsPacker_3618_);
v___x_3644_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1);
v___x_3645_ = l_Lean_indentExpr(v_packedMotiveType_3641_);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3644_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3646_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
else
{
v___y_3628_ = v___f_3642_;
v___y_3629_ = v_packedMotiveType_3641_;
v___y_3630_ = v___y_3637_;
v___y_3631_ = v___y_3638_;
v___y_3632_ = v___y_3639_;
v___y_3633_ = v___y_3640_;
goto v___jp_3627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object* v_argsPacker_3669_, lean_object* v_value_3670_, lean_object* v_type_3671_, lean_object* v_k_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3669_, v_value_3670_, v_type_3671_, v_k_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object* v_00_u03b1_3679_, lean_object* v_argsPacker_3680_, lean_object* v_value_3681_, lean_object* v_type_3682_, lean_object* v_k_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3680_, v_value_3681_, v_type_3682_, v_k_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object* v_00_u03b1_3690_, lean_object* v_argsPacker_3691_, lean_object* v_value_3692_, lean_object* v_type_3693_, lean_object* v_k_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_Meta_ArgsPacker_curryParam(v_00_u03b1_3690_, v_argsPacker_3691_, v_value_3692_, v_type_3693_, v_k_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
return v_res_3700_;
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
