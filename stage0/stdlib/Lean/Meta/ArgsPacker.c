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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: xType.isAppOfArity ``PSum 2\n    "};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "_private.Lean.Meta.ArgsPacker.0.Lean.Meta.ArgsPacker.Mutual.mkCodomain.go"};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2;
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ArgsPacker_Mutual_packType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__1));
v___x_1624_ = lean_unsigned_to_nat(4u);
v___x_1625_ = lean_unsigned_to_nat(327u);
v___x_1626_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__0));
v___x_1627_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_1628_ = l_mkPanicMessageWithDecl(v___x_1627_, v___x_1626_, v___x_1625_, v___x_1624_, v___x_1623_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed(lean_object* v_types_1632_, lean_object* v_k_1633_, lean_object* v___x_1634_, lean_object* v_u_1635_, lean_object* v___x_1636_, lean_object* v___x_1637_, lean_object* v___x_1638_, lean_object* v___x_1639_, lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v___x_1741__boxed_1646_; uint8_t v___x_1742__boxed_1647_; uint8_t v___x_1743__boxed_1648_; lean_object* v_res_1649_; 
v___x_1741__boxed_1646_ = lean_unbox(v___x_1637_);
v___x_1742__boxed_1647_ = lean_unbox(v___x_1638_);
v___x_1743__boxed_1648_ = lean_unbox(v___x_1639_);
v_res_1649_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(v_types_1632_, v_k_1633_, v___x_1634_, v_u_1635_, v___x_1636_, v___x_1741__boxed_1646_, v___x_1742__boxed_1647_, v___x_1743__boxed_1648_, v_x_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v_types_1632_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(lean_object* v_types_1650_, lean_object* v___x_1651_, lean_object* v_k_1652_, lean_object* v_u_1653_, lean_object* v___x_1654_, uint8_t v___x_1655_, uint8_t v___x_1656_, uint8_t v___x_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = l_Array_extract___redArg(v_types_1650_, v___x_1651_, v_k_1652_);
lean_inc_ref(v_x_1658_);
v___x_1665_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_u_1653_, v___x_1664_, v_x_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = lean_array_push(v___x_1654_, v_x_1658_);
v___x_1668_ = l_Lean_Meta_mkLambdaFVars(v___x_1667_, v_a_1666_, v___x_1655_, v___x_1656_, v___x_1655_, v___x_1656_, v___x_1657_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec_ref(v___x_1667_);
return v___x_1668_;
}
else
{
lean_dec_ref(v_x_1658_);
lean_dec_ref(v___x_1654_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed(lean_object* v_types_1669_, lean_object* v___x_1670_, lean_object* v_k_1671_, lean_object* v_u_1672_, lean_object* v___x_1673_, lean_object* v___x_1674_, lean_object* v___x_1675_, lean_object* v___x_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v___x_1757__boxed_1683_; uint8_t v___x_1758__boxed_1684_; uint8_t v___x_1759__boxed_1685_; lean_object* v_res_1686_; 
v___x_1757__boxed_1683_ = lean_unbox(v___x_1674_);
v___x_1758__boxed_1684_ = lean_unbox(v___x_1675_);
v___x_1759__boxed_1685_ = lean_unbox(v___x_1676_);
v_res_1686_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1(v_types_1669_, v___x_1670_, v_k_1671_, v_u_1672_, v___x_1673_, v___x_1757__boxed_1683_, v___x_1758__boxed_1684_, v___x_1759__boxed_1685_, v_x_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v_types_1669_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(lean_object* v_u_1687_, lean_object* v_types_1688_, lean_object* v_x_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1695_ = l_Lean_instInhabitedExpr;
v___x_1696_ = lean_array_get_size(v_types_1688_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_nat_dec_le(v___x_1696_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v_k_1699_; lean_object* v___x_1700_; 
v_k_1699_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v___x_1696_);
lean_inc(v_a_1693_);
lean_inc_ref(v_a_1692_);
lean_inc(v_a_1691_);
lean_inc_ref(v_a_1690_);
lean_inc_ref(v_x_1689_);
v___x_1700_ = lean_infer_type(v_x_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1702_ = l_Lean_Meta_whnfD(v_a_1701_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1));
v___x_1705_ = lean_unsigned_to_nat(2u);
v___x_1706_ = l_Lean_Expr_isAppOfArity(v_a_1703_, v___x_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec(v_a_1703_);
lean_dec(v_k_1699_);
lean_dec_ref(v_x_1689_);
lean_dec_ref(v_types_1688_);
lean_dec(v_u_1687_);
v___x_1707_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__2);
v___x_1708_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_1707_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1708_;
}
else
{
lean_object* v_dummy_1709_; lean_object* v_nargs_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; 
v_dummy_1709_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0, &l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0_once, _init_l_Lean_Meta_ArgsPacker_Mutual_pack___closed__0);
v_nargs_1710_ = l_Lean_Expr_getAppNumArgs(v_a_1703_);
lean_inc(v_nargs_1710_);
v___x_1711_ = lean_mk_array(v_nargs_1710_, v_dummy_1709_);
v___x_1712_ = lean_nat_sub(v_nargs_1710_, v___x_1697_);
lean_dec(v_nargs_1710_);
lean_inc(v_a_1703_);
v___x_1713_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1703_, v___x_1711_, v___x_1712_);
v___x_1714_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
lean_inc_n(v_u_1687_, 3);
v___x_1715_ = l_Lean_Level_succ___override(v_u_1687_);
v___x_1716_ = l_Lean_Expr_getAppFn(v_a_1703_);
lean_dec(v_a_1703_);
v___x_1717_ = l_Lean_Expr_constLevels_x21(v___x_1716_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1715_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = l_Lean_mkConst(v___x_1714_, v___x_1718_);
v___x_1720_ = l_Lean_mkAppN(v___x_1719_, v___x_1713_);
v___x_1721_ = lean_mk_empty_array_with_capacity(v___x_1697_);
lean_inc_ref(v_x_1689_);
lean_inc_ref_n(v___x_1721_, 2);
v___x_1722_ = lean_array_push(v___x_1721_, v_x_1689_);
v___x_1723_ = l_Lean_mkSort(v_u_1687_);
v___x_1724_ = 1;
v___x_1725_ = lean_box(v___x_1698_);
v___x_1726_ = lean_box(v___x_1706_);
v___x_1727_ = lean_box(v___x_1724_);
lean_inc(v_k_1699_);
lean_inc_ref(v_types_1688_);
v___f_1728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0___boxed), 14, 8);
lean_closure_set(v___f_1728_, 0, v_types_1688_);
lean_closure_set(v___f_1728_, 1, v_k_1699_);
lean_closure_set(v___f_1728_, 2, v___x_1696_);
lean_closure_set(v___f_1728_, 3, v_u_1687_);
lean_closure_set(v___f_1728_, 4, v___x_1721_);
lean_closure_set(v___f_1728_, 5, v___x_1725_);
lean_closure_set(v___f_1728_, 6, v___x_1726_);
lean_closure_set(v___f_1728_, 7, v___x_1727_);
v___x_1729_ = l_Lean_Meta_mkLambdaFVars(v___x_1722_, v___x_1723_, v___x_1698_, v___x_1706_, v___x_1698_, v___x_1706_, v___x_1724_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
lean_dec_ref(v___x_1722_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = l_Lean_Expr_app___override(v___x_1720_, v_a_1730_);
v___x_1732_ = l_Lean_Expr_app___override(v___x_1731_, v_x_1689_);
v___x_1733_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_1734_ = l_Lean_Core_mkFreshUserName(v___x_1733_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___f_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_box(v___x_1698_);
v___x_1738_ = lean_box(v___x_1706_);
v___x_1739_ = lean_box(v___x_1724_);
v___f_1740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_1740_, 0, v_types_1688_);
lean_closure_set(v___f_1740_, 1, v___x_1736_);
lean_closure_set(v___f_1740_, 2, v_k_1699_);
lean_closure_set(v___f_1740_, 3, v_u_1687_);
lean_closure_set(v___f_1740_, 4, v___x_1721_);
lean_closure_set(v___f_1740_, 5, v___x_1737_);
lean_closure_set(v___f_1740_, 6, v___x_1738_);
lean_closure_set(v___f_1740_, 7, v___x_1739_);
v___x_1741_ = lean_array_get_borrowed(v___x_1695_, v___x_1713_, v___x_1736_);
lean_inc(v___x_1741_);
v___x_1742_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1735_, v___x_1741_, v___f_1740_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v___x_1744_ = l_Lean_Core_mkFreshUserName(v___x_1733_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v___x_1746_ = lean_array_get(v___x_1695_, v___x_1713_, v___x_1697_);
lean_dec_ref(v___x_1713_);
v___x_1747_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1745_, v___x_1746_, v___f_1728_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1756_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1756_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1752_ = l_Lean_mkAppB(v___x_1732_, v_a_1743_, v_a_1748_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1752_);
v___x_1754_ = v___x_1750_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
else
{
lean_dec(v_a_1743_);
lean_dec_ref(v___x_1732_);
return v___x_1747_;
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_a_1743_);
lean_dec_ref(v___x_1732_);
lean_dec_ref(v___f_1728_);
lean_dec_ref(v___x_1713_);
v_a_1757_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1744_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1744_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_dec_ref(v___x_1732_);
lean_dec_ref(v___f_1728_);
lean_dec_ref(v___x_1713_);
return v___x_1742_;
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v___x_1732_);
lean_dec_ref(v___f_1728_);
lean_dec_ref(v___x_1721_);
lean_dec_ref(v___x_1713_);
lean_dec(v_k_1699_);
lean_dec_ref(v_types_1688_);
lean_dec(v_u_1687_);
v_a_1765_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1734_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1734_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_dec_ref(v___f_1728_);
lean_dec_ref(v___x_1721_);
lean_dec_ref(v___x_1720_);
lean_dec_ref(v___x_1713_);
lean_dec(v_k_1699_);
lean_dec_ref(v_x_1689_);
lean_dec_ref(v_types_1688_);
lean_dec(v_u_1687_);
return v___x_1729_;
}
}
}
else
{
lean_dec(v_k_1699_);
lean_dec_ref(v_x_1689_);
lean_dec_ref(v_types_1688_);
lean_dec(v_u_1687_);
return v___x_1702_;
}
}
else
{
lean_dec(v_k_1699_);
lean_dec_ref(v_x_1689_);
lean_dec_ref(v_types_1688_);
lean_dec(v_u_1687_);
return v___x_1700_;
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v_u_1687_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_array_get(v___x_1695_, v_types_1688_, v___x_1773_);
lean_dec_ref(v_types_1688_);
v___x_1775_ = l_Lean_Expr_bindingBody_x21(v___x_1774_);
lean_dec(v___x_1774_);
v___x_1776_ = lean_expr_instantiate1(v___x_1775_, v_x_1689_);
lean_dec_ref(v_x_1689_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___lam__0(lean_object* v_types_1778_, lean_object* v_k_1779_, lean_object* v___x_1780_, lean_object* v_u_1781_, lean_object* v___x_1782_, uint8_t v___x_1783_, uint8_t v___x_1784_, uint8_t v___x_1785_, lean_object* v_x_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = l_Array_extract___redArg(v_types_1778_, v_k_1779_, v___x_1780_);
lean_inc_ref(v_x_1786_);
v___x_1793_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_u_1781_, v___x_1792_, v_x_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = lean_array_push(v___x_1782_, v_x_1786_);
v___x_1796_ = l_Lean_Meta_mkLambdaFVars(v___x_1795_, v_a_1794_, v___x_1783_, v___x_1784_, v___x_1783_, v___x_1784_, v___x_1785_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec_ref(v___x_1795_);
return v___x_1796_;
}
else
{
lean_dec_ref(v_x_1786_);
lean_dec_ref(v___x_1782_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___boxed(lean_object* v_u_1797_, lean_object* v_types_1798_, lean_object* v_x_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_u_1797_, v_types_1798_, v_x_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(lean_object* v_x_1806_, lean_object* v_body_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_Meta_getLevel(v_body_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0___boxed(lean_object* v_x_1814_, lean_object* v_body_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___lam__0(v_x_1814_, v_body_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec_ref(v_x_1814_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(lean_object* v_types_1823_, lean_object* v_x_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___f_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; 
v___f_1830_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___closed__0));
v___x_1831_ = l_Lean_instInhabitedExpr;
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1833_ = lean_array_get_borrowed(v___x_1831_, v_types_1823_, v___x_1832_);
v___x_1834_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_1835_ = 0;
lean_inc(v___x_1833_);
v___x_1836_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v___x_1833_, v___x_1834_, v___f_1830_, v___x_1835_, v___x_1835_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go(v_a_1837_, v_types_1823_, v_x_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1838_;
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_x_1824_);
lean_dec_ref(v_types_1823_);
v_a_1839_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1836_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1836_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_mkCodomain___boxed(lean_object* v_types_1847_, lean_object* v_x_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_types_1847_, v_x_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(lean_object* v_a_1855_, lean_object* v___x_1856_, uint8_t v___x_1857_, lean_object* v_x_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
lean_inc_ref(v_x_1858_);
v___x_1864_ = l_Lean_Meta_ArgsPacker_Mutual_mkCodomain(v_a_1855_, v_x_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___x_1866_ = lean_mk_empty_array_with_capacity(v___x_1856_);
v___x_1867_ = lean_array_push(v___x_1866_, v_x_1858_);
v___x_1868_ = 1;
v___x_1869_ = 1;
v___x_1870_ = l_Lean_Meta_mkForallFVars(v___x_1867_, v_a_1865_, v___x_1857_, v___x_1868_, v___x_1868_, v___x_1869_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec_ref(v___x_1867_);
return v___x_1870_;
}
else
{
lean_dec_ref(v_x_1858_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed(lean_object* v_a_1871_, lean_object* v___x_1872_, lean_object* v___x_1873_, lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v___x_1823__boxed_1880_; lean_object* v_res_1881_; 
v___x_1823__boxed_1880_ = lean_unbox(v___x_1873_);
v_res_1881_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0(v_a_1871_, v___x_1872_, v___x_1823__boxed_1880_, v_x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___x_1872_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(size_t v_sz_1882_, size_t v_i_1883_, lean_object* v_bs_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_usize_dec_lt(v_i_1883_, v_sz_1882_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_bs_1884_);
return v___x_1891_;
}
else
{
lean_object* v_v_1892_; lean_object* v___x_1893_; lean_object* v_bs_x27_1894_; lean_object* v___x_1895_; 
v_v_1892_ = lean_array_uget(v_bs_1884_, v_i_1883_);
v___x_1893_ = lean_unsigned_to_nat(0u);
v_bs_x27_1894_ = lean_array_uset(v_bs_1884_, v_i_1883_, v___x_1893_);
v___x_1895_ = l_Lean_Meta_whnfForall(v_v_1892_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; size_t v___x_1897_; size_t v___x_1898_; lean_object* v___x_1899_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = ((size_t)1ULL);
v___x_1898_ = lean_usize_add(v_i_1883_, v___x_1897_);
v___x_1899_ = lean_array_uset(v_bs_x27_1894_, v_i_1883_, v_a_1896_);
v_i_1883_ = v___x_1898_;
v_bs_1884_ = v___x_1899_;
goto _start;
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref(v_bs_x27_1894_);
v_a_1901_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1895_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1895_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0___boxed(lean_object* v_sz_1909_, lean_object* v_i_1910_, lean_object* v_bs_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
size_t v_sz_boxed_1917_; size_t v_i_boxed_1918_; lean_object* v_res_1919_; 
v_sz_boxed_1917_ = lean_unbox_usize(v_sz_1909_);
lean_dec(v_sz_1909_);
v_i_boxed_1918_ = lean_unbox_usize(v_i_1910_);
lean_dec(v_i_1910_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_boxed_1917_, v_i_boxed_1918_, v_bs_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1919_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__0));
v___x_1922_ = l_Lean_stringToMessageData(v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(lean_object* v_as_1923_, size_t v_i_1924_, size_t v_stop_1925_, lean_object* v_b_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_a_1933_; uint8_t v___x_1937_; 
v___x_1937_ = lean_usize_dec_eq(v_i_1924_, v_stop_1925_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_array_uget_borrowed(v_as_1923_, v_i_1924_);
v___x_1939_ = l_Lean_Expr_isForall(v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1940_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___closed__1);
lean_inc(v___x_1938_);
v___x_1941_ = l_Lean_MessageData_ofExpr(v___x_1938_);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_1942_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v_a_1933_ = v_a_1944_;
goto v___jp_1932_;
}
else
{
return v___x_1943_;
}
}
else
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_box(0);
v_a_1933_ = v___x_1945_;
goto v___jp_1932_;
}
}
else
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_b_1926_);
return v___x_1946_;
}
v___jp_1932_:
{
size_t v___x_1934_; size_t v___x_1935_; 
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_add(v_i_1924_, v___x_1934_);
v_i_1924_ = v___x_1935_;
v_b_1926_ = v_a_1933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2___boxed(lean_object* v_as_1947_, lean_object* v_i_1948_, lean_object* v_stop_1949_, lean_object* v_b_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
size_t v_i_boxed_1956_; size_t v_stop_boxed_1957_; lean_object* v_res_1958_; 
v_i_boxed_1956_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_stop_boxed_1957_ = lean_unbox_usize(v_stop_1949_);
lean_dec(v_stop_1949_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_as_1947_, v_i_boxed_1956_, v_stop_boxed_1957_, v_b_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec_ref(v_as_1947_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(size_t v_sz_1959_, size_t v_i_1960_, lean_object* v_bs_1961_){
_start:
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_usize_dec_lt(v_i_1960_, v_sz_1959_);
if (v___x_1962_ == 0)
{
return v_bs_1961_;
}
else
{
lean_object* v_v_1963_; lean_object* v___x_1964_; lean_object* v_bs_x27_1965_; lean_object* v___x_1966_; size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v_v_1963_ = lean_array_uget(v_bs_1961_, v_i_1960_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v_bs_x27_1965_ = lean_array_uset(v_bs_1961_, v_i_1960_, v___x_1964_);
v___x_1966_ = l_Lean_Expr_bindingDomain_x21(v_v_1963_);
lean_dec(v_v_1963_);
v___x_1967_ = ((size_t)1ULL);
v___x_1968_ = lean_usize_add(v_i_1960_, v___x_1967_);
v___x_1969_ = lean_array_uset(v_bs_x27_1965_, v_i_1960_, v___x_1966_);
v_i_1960_ = v___x_1968_;
v_bs_1961_ = v___x_1969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1___boxed(lean_object* v_sz_1971_, lean_object* v_i_1972_, lean_object* v_bs_1973_){
_start:
{
size_t v_sz_boxed_1974_; size_t v_i_boxed_1975_; lean_object* v_res_1976_; 
v_sz_boxed_1974_ = lean_unbox_usize(v_sz_1971_);
lean_dec(v_sz_1971_);
v_i_boxed_1975_ = lean_unbox_usize(v_i_1972_);
lean_dec(v_i_1972_);
v_res_1976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_boxed_1974_, v_i_boxed_1975_, v_bs_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType(lean_object* v_types_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = lean_array_get_size(v_types_1977_);
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = lean_nat_dec_eq(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
size_t v_sz_1986_; size_t v___x_1987_; lean_object* v___x_1988_; 
v_sz_1986_ = lean_array_size(v_types_1977_);
v___x_1987_ = ((size_t)0ULL);
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_1986_, v___x_1987_, v_types_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; lean_object* v___f_1991_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_n(v_a_1989_, 2);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = lean_box(v___x_1985_);
v___f_1991_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryType___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1991_, 0, v_a_1989_);
lean_closure_set(v___f_1991_, 1, v___x_1984_);
lean_closure_set(v___f_1991_, 2, v___x_1990_);
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = lean_array_get_size(v_a_1989_);
v___x_2011_ = lean_nat_dec_lt(v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
goto v___jp_1992_;
}
else
{
lean_object* v___x_2012_; size_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = lean_usize_of_nat(v___x_2010_);
v___x_2014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__2(v_a_1989_, v___x_1987_, v___x_2013_, v___x_2012_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_dec_ref_known(v___x_2014_, 1);
goto v___jp_1992_;
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v___f_1991_);
lean_dec(v_a_1989_);
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
v___jp_1992_:
{
size_t v_sz_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_sz_1993_ = lean_array_size(v_a_1989_);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v_sz_1993_, v___x_1987_, v_a_1989_);
v___x_1995_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_1994_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec_ref(v___x_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_1998_ = l_Lean_Core_mkFreshUserName(v___x_1997_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_1999_, v_a_1996_, v___f_1991_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
return v___x_2000_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_a_1996_);
lean_dec_ref(v___f_1991_);
v_a_2001_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1998_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1998_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_dec_ref(v___f_1991_);
return v___x_1995_;
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_a_2023_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1988_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1988_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2031_ = l_Lean_instInhabitedExpr;
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_array_get(v___x_2031_, v_types_1977_, v___x_2032_);
lean_dec_ref(v_types_1977_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryType___boxed(lean_object* v_types_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_types_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
return v_res_2041_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__0));
v___x_2044_ = l_Lean_stringToMessageData(v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__2));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(lean_object* v___x_2048_, lean_object* v_as_2049_, size_t v_i_2050_, size_t v_stop_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_a_2059_; uint8_t v___x_2063_; 
v___x_2063_ = lean_usize_dec_eq(v_i_2050_, v_stop_2051_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_array_uget_borrowed(v_as_2049_, v_i_2050_);
lean_inc_ref(v___x_2048_);
lean_inc(v___x_2064_);
v___x_2065_ = l_Lean_Meta_isExprDefEq(v___x_2064_, v___x_2048_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; uint8_t v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = lean_unbox(v_a_2066_);
lean_dec(v_a_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__1);
lean_inc(v___x_2064_);
v___x_2069_ = l_Lean_MessageData_ofExpr(v___x_2064_);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___closed__3);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
lean_inc_ref(v___x_2048_);
v___x_2073_ = l_Lean_MessageData_ofExpr(v___x_2048_);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2074_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v_a_2059_ = v_a_2076_;
goto v___jp_2058_;
}
else
{
lean_dec_ref(v___x_2048_);
return v___x_2075_;
}
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_box(0);
v_a_2059_ = v___x_2077_;
goto v___jp_2058_;
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v___x_2048_);
v_a_2078_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2065_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2065_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v___x_2086_; 
lean_dec_ref(v___x_2048_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_b_2052_);
return v___x_2086_;
}
v___jp_2058_:
{
size_t v___x_2060_; size_t v___x_2061_; 
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2050_, v___x_2060_);
v_i_2050_ = v___x_2061_;
v_b_2052_ = v_a_2059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1___boxed(lean_object* v___x_2087_, lean_object* v_as_2088_, lean_object* v_i_2089_, lean_object* v_stop_2090_, lean_object* v_b_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
size_t v_i_boxed_2097_; size_t v_stop_boxed_2098_; lean_object* v_res_2099_; 
v_i_boxed_2097_ = lean_unbox_usize(v_i_2089_);
lean_dec(v_i_2089_);
v_stop_boxed_2098_ = lean_unbox_usize(v_stop_2090_);
lean_dec(v_stop_2090_);
v_res_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2087_, v_as_2088_, v_i_boxed_2097_, v_stop_boxed_2098_, v_b_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v_as_2088_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(size_t v_sz_2100_, size_t v_i_2101_, lean_object* v_bs_2102_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_usize_dec_lt(v_i_2101_, v_sz_2100_);
if (v___x_2103_ == 0)
{
return v_bs_2102_;
}
else
{
lean_object* v_v_2104_; lean_object* v___x_2105_; lean_object* v_bs_x27_2106_; lean_object* v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; 
v_v_2104_ = lean_array_uget(v_bs_2102_, v_i_2101_);
v___x_2105_ = lean_unsigned_to_nat(0u);
v_bs_x27_2106_ = lean_array_uset(v_bs_2102_, v_i_2101_, v___x_2105_);
v___x_2107_ = l_Lean_Expr_bindingBody_x21(v_v_2104_);
lean_dec(v_v_2104_);
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_add(v_i_2101_, v___x_2108_);
v___x_2110_ = lean_array_uset(v_bs_x27_2106_, v_i_2101_, v___x_2107_);
v_i_2101_ = v___x_2109_;
v_bs_2102_ = v___x_2110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0___boxed(lean_object* v_sz_2112_, lean_object* v_i_2113_, lean_object* v_bs_2114_){
_start:
{
size_t v_sz_boxed_2115_; size_t v_i_boxed_2116_; lean_object* v_res_2117_; 
v_sz_boxed_2115_ = lean_unbox_usize(v_sz_2112_);
lean_dec(v_sz_2112_);
v_i_boxed_2116_ = lean_unbox_usize(v_i_2113_);
lean_dec(v_i_2113_);
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_boxed_2115_, v_i_boxed_2116_, v_bs_2114_);
return v_res_2117_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__0));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(lean_object* v_as_2121_, size_t v_i_2122_, size_t v_stop_2123_, lean_object* v_b_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_a_2131_; uint8_t v___x_2135_; 
v___x_2135_ = lean_usize_dec_eq(v_i_2122_, v_stop_2123_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = lean_array_uget_borrowed(v_as_2121_, v_i_2122_);
v___x_2137_ = l_Lean_Expr_isArrow(v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2138_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___closed__1);
lean_inc(v___x_2136_);
v___x_2139_ = l_Lean_MessageData_ofExpr(v___x_2136_);
v___x_2140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2140_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v_a_2131_ = v_a_2142_;
goto v___jp_2130_;
}
else
{
return v___x_2141_;
}
}
else
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_box(0);
v_a_2131_ = v___x_2143_;
goto v___jp_2130_;
}
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_b_2124_);
return v___x_2144_;
}
v___jp_2130_:
{
size_t v___x_2132_; size_t v___x_2133_; 
v___x_2132_ = ((size_t)1ULL);
v___x_2133_ = lean_usize_add(v_i_2122_, v___x_2132_);
v_i_2122_ = v___x_2133_;
v_b_2124_ = v_a_2131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2___boxed(lean_object* v_as_2145_, lean_object* v_i_2146_, lean_object* v_stop_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
size_t v_i_boxed_2154_; size_t v_stop_boxed_2155_; lean_object* v_res_2156_; 
v_i_boxed_2154_ = lean_unbox_usize(v_i_2146_);
lean_dec(v_i_2146_);
v_stop_boxed_2155_ = lean_unbox_usize(v_stop_2147_);
lean_dec(v_stop_2147_);
v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_as_2145_, v_i_boxed_2154_, v_stop_boxed_2155_, v_b_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec_ref(v_as_2145_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(lean_object* v_types_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v___x_2163_; size_t v_sz_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = l_Lean_instInhabitedExpr;
v_sz_2164_ = lean_array_size(v_types_2157_);
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__0(v_sz_2164_, v___x_2165_, v_types_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; size_t v___y_2170_; lean_object* v___y_2171_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2198_ = lean_array_get_size(v_a_2167_);
v___x_2199_ = lean_nat_dec_lt(v___x_2168_, v___x_2198_);
if (v___x_2199_ == 0)
{
goto v___jp_2177_;
}
else
{
lean_object* v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_usize_of_nat(v___x_2198_);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__2(v_a_2167_, v___x_2165_, v___x_2201_, v___x_2200_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_dec_ref_known(v___x_2202_, 1);
goto v___jp_2177_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec(v_a_2167_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
v___jp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_array_get(v___x_2163_, v___y_2171_, v___x_2168_);
lean_dec_ref(v___y_2171_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryType_spec__1(v___y_2170_, v___x_2165_, v_a_2167_);
v___x_2174_ = l_Lean_Meta_ArgsPacker_Mutual_packType(v___x_2173_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec_ref(v___x_2173_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2176_ = l_Lean_mkArrow(v_a_2175_, v___x_2172_, v_a_2160_, v_a_2161_);
return v___x_2176_;
}
else
{
lean_dec(v___x_2172_);
return v___x_2174_;
}
}
v___jp_2177_:
{
size_t v_sz_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_sz_2178_ = lean_array_size(v_a_2167_);
lean_inc(v_a_2167_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__0(v_sz_2178_, v___x_2165_, v_a_2167_);
v___x_2180_ = lean_array_get_size(v___x_2179_);
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = lean_nat_sub(v___x_2180_, v___x_2181_);
v___x_2183_ = lean_array_get_borrowed(v___x_2163_, v___x_2179_, v___x_2182_);
lean_dec(v___x_2182_);
lean_inc_ref(v___x_2179_);
v___x_2184_ = lean_array_pop(v___x_2179_);
v___x_2185_ = lean_array_get_size(v___x_2184_);
v___x_2186_ = lean_nat_dec_lt(v___x_2168_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_dec_ref(v___x_2184_);
v___y_2170_ = v_sz_2178_;
v___y_2171_ = v___x_2179_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_box(0);
v___x_2188_ = lean_usize_of_nat(v___x_2185_);
lean_inc(v___x_2183_);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_ArgsPacker_Mutual_uncurryTypeND_spec__1(v___x_2183_, v___x_2184_, v___x_2165_, v___x_2188_, v___x_2187_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec_ref(v___x_2184_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_dec_ref_known(v___x_2189_, 1);
v___y_2170_ = v_sz_2178_;
v___y_2171_ = v___x_2179_;
goto v___jp_2169_;
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v___x_2179_);
lean_dec(v_a_2167_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
v_a_2211_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2166_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2166_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND___boxed(lean_object* v_types_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_types_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2225_;
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__0));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed(lean_object* v_ctor_2229_, lean_object* v___x_2230_, lean_object* v_arg_2231_, lean_object* v_arg_2232_, lean_object* v___x_2233_, lean_object* v_a_2234_, lean_object* v_alts_2235_, lean_object* v___x_2236_, lean_object* v___x_2237_, lean_object* v___x_2238_, lean_object* v_y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
uint8_t v___x_2330__boxed_2245_; uint8_t v___x_2331__boxed_2246_; uint8_t v___x_2332__boxed_2247_; lean_object* v_res_2248_; 
v___x_2330__boxed_2245_ = lean_unbox(v___x_2236_);
v___x_2331__boxed_2246_ = lean_unbox(v___x_2237_);
v___x_2332__boxed_2247_ = lean_unbox(v___x_2238_);
v_res_2248_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(v_ctor_2229_, v___x_2230_, v_arg_2231_, v_arg_2232_, v___x_2233_, v_a_2234_, v_alts_2235_, v___x_2330__boxed_2245_, v___x_2331__boxed_2246_, v___x_2332__boxed_2247_, v_y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_alts_2235_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(lean_object* v___x_2249_, lean_object* v___x_2250_, lean_object* v_arg_2251_, lean_object* v_arg_2252_, lean_object* v___x_2253_, lean_object* v_a_2254_, uint8_t v___x_2255_, uint8_t v___x_2256_, uint8_t v___x_2257_, lean_object* v___x_2258_, lean_object* v_ctor_2259_, lean_object* v_d_2260_, lean_object* v_alts_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_array_get_size(v_alts_2261_);
v___x_2268_ = lean_nat_dec_eq(v___x_2267_, v___x_2249_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2269_ = lean_box(v___x_2255_);
v___x_2270_ = lean_box(v___x_2256_);
v___x_2271_ = lean_box(v___x_2257_);
v___f_2272_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2272_, 0, v_ctor_2259_);
lean_closure_set(v___f_2272_, 1, v___x_2250_);
lean_closure_set(v___f_2272_, 2, v_arg_2251_);
lean_closure_set(v___f_2272_, 3, v_arg_2252_);
lean_closure_set(v___f_2272_, 4, v___x_2253_);
lean_closure_set(v___f_2272_, 5, v_a_2254_);
lean_closure_set(v___f_2272_, 6, v_alts_2261_);
lean_closure_set(v___f_2272_, 7, v___x_2269_);
lean_closure_set(v___f_2272_, 8, v___x_2270_);
lean_closure_set(v___f_2272_, 9, v___x_2271_);
v___x_2273_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurryType___lam__1___closed__4));
v___x_2274_ = l_Lean_Core_mkFreshUserName(v___x_2273_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2276_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2276_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_a_2275_, v_d_2260_, v___f_2272_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2276_;
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v___f_2272_);
lean_dec_ref(v_d_2260_);
v_a_2277_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2274_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2274_);
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
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v_d_2260_);
lean_dec(v_ctor_2259_);
lean_dec_ref(v_a_2254_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v_arg_2252_);
lean_dec_ref(v_arg_2251_);
lean_dec(v___x_2250_);
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = lean_array_get(v___x_2258_, v_alts_2261_, v___x_2285_);
lean_dec_ref(v_alts_2261_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__2));
v___x_2290_ = l_Lean_stringToMessageData(v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(lean_object* v_x_2291_, lean_object* v_codomain_2292_, lean_object* v_alts_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___x_2309_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2309_ = l_Lean_instInhabitedExpr;
v___x_2375_ = lean_array_get_size(v_alts_2293_);
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = lean_nat_dec_eq(v___x_2375_, v___x_2376_);
if (v___x_2377_ == 0)
{
v___y_2311_ = v_a_2294_;
v___y_2312_ = v_a_2295_;
v___y_2313_ = v_a_2296_;
v___y_2314_ = v_a_2297_;
goto v___jp_2310_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__3);
v___x_2379_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2378_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_dec_ref_known(v___x_2379_, 1);
v___y_2311_ = v_a_2294_;
v___y_2312_ = v_a_2295_;
v___y_2313_ = v_a_2296_;
v___y_2314_ = v_a_2297_;
goto v___jp_2310_;
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v_codomain_2292_);
lean_dec_ref(v_x_2291_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
v___jp_2299_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2305_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___closed__1);
v___x_2306_ = l_Lean_MessageData_ofExpr(v___y_2300_);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2307_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2308_;
}
v___jp_2310_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2315_ = lean_array_get_size(v_alts_2293_);
v___x_2316_ = lean_unsigned_to_nat(1u);
v___x_2317_ = lean_nat_dec_eq(v___x_2315_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; 
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
lean_inc(v___y_2312_);
lean_inc_ref(v___y_2311_);
lean_inc_ref(v_x_2291_);
v___x_2318_ = lean_infer_type(v_x_2291_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc_n(v_a_2319_, 2);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2319_, v___y_2312_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = l_Lean_Expr_cleanupAnnotations(v_a_2321_);
lean_dec(v_a_2321_);
v___x_2323_ = l_Lean_Expr_isApp(v___x_2322_);
if (v___x_2323_ == 0)
{
lean_dec_ref(v___x_2322_);
lean_dec_ref(v_codomain_2292_);
lean_dec_ref(v_x_2291_);
v___y_2300_ = v_a_2319_;
v___y_2301_ = v___y_2311_;
v___y_2302_ = v___y_2312_;
v___y_2303_ = v___y_2313_;
v___y_2304_ = v___y_2314_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2322_);
v___x_2325_ = l_Lean_Expr_isApp(v___x_2324_);
if (v___x_2325_ == 0)
{
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v_codomain_2292_);
lean_dec_ref(v_x_2291_);
v___y_2300_ = v_a_2319_;
v___y_2301_ = v___y_2311_;
v___y_2302_ = v___y_2312_;
v___y_2303_ = v___y_2313_;
v___y_2304_ = v___y_2314_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2324_);
v___x_2327_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_packType___closed__1));
v___x_2328_ = l_Lean_Expr_isConstOf(v___x_2326_, v___x_2327_);
lean_dec_ref(v___x_2326_);
if (v___x_2328_ == 0)
{
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v_codomain_2292_);
lean_dec_ref(v_x_2291_);
v___y_2300_ = v_a_2319_;
v___y_2301_ = v___y_2311_;
v___y_2302_ = v___y_2312_;
v___y_2303_ = v___y_2313_;
v___y_2304_ = v___y_2314_;
goto v___jp_2299_;
}
else
{
lean_object* v_arg_2329_; lean_object* v_arg_2330_; lean_object* v___x_2331_; 
v_arg_2329_ = lean_ctor_get(v___x_2322_, 1);
lean_inc_ref(v_arg_2329_);
lean_dec_ref(v___x_2322_);
v_arg_2330_ = lean_ctor_get(v___x_2324_, 1);
lean_inc_ref(v_arg_2330_);
lean_dec_ref(v___x_2324_);
lean_inc_ref(v_codomain_2292_);
v___x_2331_ = l_Lean_Meta_getLevel(v_codomain_2292_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; lean_object* v___x_2338_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = l_Lean_Expr_getAppFn(v_a_2319_);
lean_dec(v_a_2319_);
v___x_2334_ = l_Lean_Expr_constLevels_x21(v___x_2333_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = lean_mk_empty_array_with_capacity(v___x_2316_);
lean_inc_ref(v_x_2291_);
lean_inc_ref(v___x_2335_);
v___x_2336_ = lean_array_push(v___x_2335_, v_x_2291_);
v___x_2337_ = 1;
v___x_2338_ = l_Lean_Meta_mkLambdaFVars(v___x_2336_, v_codomain_2292_, v___x_2317_, v___x_2328_, v___x_2317_, v___x_2328_, v___x_2337_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec_ref(v___x_2336_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc_n(v_a_2339_, 2);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_numLeft(v___x_2315_);
v___x_2341_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__6));
v___x_2342_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_2340_);
v___x_2343_ = l_Array_extract___redArg(v_alts_2293_, v___x_2342_, v___x_2340_);
lean_inc_ref(v___x_2335_);
lean_inc_ref(v_arg_2329_);
lean_inc_ref_n(v_arg_2330_, 2);
lean_inc(v___x_2334_);
v___x_2344_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(v___x_2316_, v___x_2334_, v_arg_2330_, v_arg_2329_, v___x_2335_, v_a_2339_, v___x_2317_, v___x_2328_, v___x_2337_, v___x_2309_, v___x_2341_, v_arg_2330_, v___x_2343_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_ArgsPacker_Mutual_pack_spec__0___closed__4));
v___x_2347_ = l_Array_extract___redArg(v_alts_2293_, v___x_2340_, v___x_2315_);
lean_inc(v_a_2339_);
lean_inc_ref_n(v_arg_2329_, 2);
lean_inc_ref(v_arg_2330_);
lean_inc(v___x_2334_);
v___x_2348_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(v___x_2316_, v___x_2334_, v_arg_2330_, v_arg_2329_, v___x_2335_, v_a_2339_, v___x_2317_, v___x_2328_, v___x_2337_, v___x_2309_, v___x_2346_, v_arg_2329_, v___x_2347_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
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
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2353_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_mkCodomain_go___closed__3));
v___x_2354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2354_, 0, v_a_2332_);
lean_ctor_set(v___x_2354_, 1, v___x_2334_);
v___x_2355_ = l_Lean_Expr_const___override(v___x_2353_, v___x_2354_);
v___x_2356_ = l_Lean_mkApp6(v___x_2355_, v_arg_2330_, v_arg_2329_, v_a_2339_, v_x_2291_, v_a_2345_, v_a_2349_);
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
else
{
lean_dec(v_a_2345_);
lean_dec(v_a_2339_);
lean_dec(v___x_2334_);
lean_dec(v_a_2332_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_x_2291_);
return v___x_2348_;
}
}
else
{
lean_dec(v___x_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v___x_2335_);
lean_dec(v___x_2334_);
lean_dec(v_a_2332_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_x_2291_);
return v___x_2344_;
}
}
else
{
lean_dec_ref(v___x_2335_);
lean_dec(v___x_2334_);
lean_dec(v_a_2332_);
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2329_);
lean_dec_ref(v_x_2291_);
return v___x_2338_;
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v_arg_2330_);
lean_dec_ref(v_arg_2329_);
lean_dec(v_a_2319_);
lean_dec_ref(v_codomain_2292_);
lean_dec_ref(v_x_2291_);
v_a_2361_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2331_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2331_);
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
}
}
else
{
lean_dec(v_a_2319_);
lean_dec_ref(v_codomain_2292_);
lean_dec_ref(v_x_2291_);
return v___x_2320_;
}
}
else
{
lean_dec_ref(v_codomain_2292_);
lean_dec_ref(v_x_2291_);
return v___x_2318_;
}
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v_codomain_2292_);
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = lean_array_get_borrowed(v___x_2309_, v_alts_2293_, v___x_2369_);
v___x_2371_ = lean_mk_empty_array_with_capacity(v___x_2316_);
v___x_2372_ = lean_array_push(v___x_2371_, v_x_2291_);
lean_inc(v___x_2370_);
v___x_2373_ = l_Lean_Expr_beta(v___x_2370_, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__0(lean_object* v_ctor_2388_, lean_object* v___x_2389_, lean_object* v_arg_2390_, lean_object* v_arg_2391_, lean_object* v___x_2392_, lean_object* v_a_2393_, lean_object* v_alts_2394_, uint8_t v___x_2395_, uint8_t v___x_2396_, uint8_t v___x_2397_, lean_object* v_y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2404_ = l_Lean_Expr_const___override(v_ctor_2388_, v___x_2389_);
lean_inc_ref_n(v_y_2398_, 2);
v___x_2405_ = l_Lean_mkApp3(v___x_2404_, v_arg_2390_, v_arg_2391_, v_y_2398_);
lean_inc_ref(v___x_2392_);
v___x_2406_ = lean_array_push(v___x_2392_, v___x_2405_);
v___x_2407_ = l_Lean_Expr_beta(v_a_2393_, v___x_2406_);
v___x_2408_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_y_2398_, v___x_2407_, v_alts_2394_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = lean_array_push(v___x_2392_, v_y_2398_);
v___x_2411_ = l_Lean_Meta_mkLambdaFVars(v___x_2410_, v_a_2409_, v___x_2395_, v___x_2396_, v___x_2395_, v___x_2396_, v___x_2397_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec_ref(v___x_2410_);
return v___x_2411_;
}
else
{
lean_dec_ref(v_y_2398_);
lean_dec_ref(v___x_2392_);
return v___x_2408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1___boxed(lean_object** _args){
lean_object* v___x_2412_ = _args[0];
lean_object* v___x_2413_ = _args[1];
lean_object* v_arg_2414_ = _args[2];
lean_object* v_arg_2415_ = _args[3];
lean_object* v___x_2416_ = _args[4];
lean_object* v_a_2417_ = _args[5];
lean_object* v___x_2418_ = _args[6];
lean_object* v___x_2419_ = _args[7];
lean_object* v___x_2420_ = _args[8];
lean_object* v___x_2421_ = _args[9];
lean_object* v_ctor_2422_ = _args[10];
lean_object* v_d_2423_ = _args[11];
lean_object* v_alts_2424_ = _args[12];
lean_object* v___y_2425_ = _args[13];
lean_object* v___y_2426_ = _args[14];
lean_object* v___y_2427_ = _args[15];
lean_object* v___y_2428_ = _args[16];
lean_object* v___y_2429_ = _args[17];
_start:
{
uint8_t v___x_2353__boxed_2430_; uint8_t v___x_2354__boxed_2431_; uint8_t v___x_2355__boxed_2432_; lean_object* v_res_2433_; 
v___x_2353__boxed_2430_ = lean_unbox(v___x_2418_);
v___x_2354__boxed_2431_ = lean_unbox(v___x_2419_);
v___x_2355__boxed_2432_ = lean_unbox(v___x_2420_);
v_res_2433_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___lam__1(v___x_2412_, v___x_2413_, v_arg_2414_, v_arg_2415_, v___x_2416_, v_a_2417_, v___x_2353__boxed_2430_, v___x_2354__boxed_2431_, v___x_2355__boxed_2432_, v___x_2421_, v_ctor_2422_, v_d_2423_, v_alts_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec_ref(v___x_2421_);
lean_dec(v___x_2412_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn___boxed(lean_object* v_x_2434_, lean_object* v_codomain_2435_, lean_object* v_alts_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v_x_2434_, v_codomain_2435_, v_alts_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec_ref(v_alts_2436_);
return v_res_2442_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2444_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___lam__0___closed__1));
v___x_2445_ = lean_unsigned_to_nat(21u);
v___x_2446_ = lean_unsigned_to_nat(424u);
v___x_2447_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__0));
v___x_2448_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2449_ = l_mkPanicMessageWithDecl(v___x_2448_, v___x_2447_, v___x_2446_, v___x_2445_, v___x_2444_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0(lean_object* v___x_2450_, lean_object* v_es_2451_, lean_object* v_xs_2452_, lean_object* v_codomain_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = lean_array_get_size(v_xs_2452_);
v___x_2460_ = lean_nat_dec_eq(v___x_2459_, v___x_2450_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_dec_ref(v_codomain_2453_);
v___x_2461_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType___lam__0___closed__1);
v___x_2462_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2461_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = lean_array_fget_borrowed(v_xs_2452_, v___x_2463_);
lean_inc(v___x_2464_);
v___x_2465_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2464_, v_codomain_2453_, v_es_2451_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_mk_empty_array_with_capacity(v___x_2450_);
lean_inc(v___x_2464_);
v___x_2468_ = lean_array_push(v___x_2467_, v___x_2464_);
v___x_2469_ = 0;
v___x_2470_ = 1;
v___x_2471_ = l_Lean_Meta_mkLambdaFVars(v___x_2468_, v_a_2466_, v___x_2469_, v___x_2460_, v___x_2469_, v___x_2460_, v___x_2470_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
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
lean_dec_ref(v_es_2473_);
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
v___x_2571_ = lean_unsigned_to_nat(444u);
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
v___x_2586_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1, &l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1_once, _init_l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___closed__1);
v___x_2587_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2586_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_array_fget_borrowed(v_xs_2577_, v___x_2588_);
lean_inc(v___x_2589_);
v___x_2590_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_casesOn(v___x_2589_, v_codomain_2578_, v_es_2576_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; uint8_t v___x_2595_; lean_object* v___x_2596_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = lean_mk_empty_array_with_capacity(v___x_2575_);
lean_inc(v___x_2589_);
v___x_2593_ = lean_array_push(v___x_2592_, v___x_2589_);
v___x_2594_ = 0;
v___x_2595_ = 1;
v___x_2596_ = l_Lean_Meta_mkLambdaFVars(v___x_2593_, v_a_2591_, v___x_2594_, v___x_2585_, v___x_2594_, v___x_2585_, v___x_2595_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec_ref(v___x_2593_);
return v___x_2596_;
}
else
{
return v___x_2590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed(lean_object* v___x_2597_, lean_object* v_es_2598_, lean_object* v_xs_2599_, lean_object* v_codomain_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0(v___x_2597_, v_es_2598_, v_xs_2599_, v_codomain_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_xs_2599_);
lean_dec_ref(v_es_2598_);
lean_dec(v___x_2597_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND(lean_object* v_es_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
size_t v_sz_2613_; size_t v___x_2614_; lean_object* v___x_2615_; 
v_sz_2613_ = lean_array_size(v_es_2607_);
v___x_2614_ = ((size_t)0ULL);
lean_inc_ref(v_es_2607_);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_uncurry_spec__0(v_sz_2613_, v___x_2614_, v_es_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2617_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v___x_2617_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryTypeND(v_a_2616_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; lean_object* v___f_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2619_ = lean_unsigned_to_nat(1u);
v___f_2620_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_Mutual_uncurryND___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2620_, 0, v___x_2619_);
lean_closure_set(v___f_2620_, 1, v_es_2607_);
v___x_2621_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__0));
v___x_2622_ = 0;
v___x_2623_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__2___redArg(v_a_2618_, v___x_2621_, v___f_2620_, v___x_2622_, v___x_2622_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
return v___x_2623_;
}
else
{
lean_dec_ref(v_es_2607_);
return v___x_2617_;
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v_es_2607_);
v_a_2624_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2615_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2615_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_uncurryND___boxed(lean_object* v_es_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_es_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(lean_object* v_a_2639_, lean_object* v_domain_2640_, lean_object* v___x_2641_, lean_object* v_type_2642_, uint8_t v___x_2643_, lean_object* v_x_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = l_List_lengthTR___redArg(v_a_2639_);
lean_inc_ref(v_x_2644_);
v___x_2651_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2650_, v_domain_2640_, v___x_2641_, v_x_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___x_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = lean_unsigned_to_nat(1u);
v___x_2654_ = lean_mk_empty_array_with_capacity(v___x_2653_);
lean_inc_ref(v___x_2654_);
v___x_2655_ = lean_array_push(v___x_2654_, v_a_2652_);
v___x_2656_ = l_Lean_Meta_instantiateForall(v_type_2642_, v___x_2655_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec_ref(v___x_2655_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; uint8_t v___x_2660_; lean_object* v___x_2661_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = lean_array_push(v___x_2654_, v_x_2644_);
v___x_2659_ = 0;
v___x_2660_ = 1;
v___x_2661_ = l_Lean_Meta_mkForallFVars(v___x_2658_, v_a_2657_, v___x_2659_, v___x_2643_, v___x_2643_, v___x_2660_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec_ref(v___x_2658_);
return v___x_2661_;
}
else
{
lean_dec_ref(v___x_2654_);
lean_dec_ref(v_x_2644_);
return v___x_2656_;
}
}
else
{
lean_dec_ref(v_x_2644_);
lean_dec_ref(v_type_2642_);
return v___x_2651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed(lean_object* v_a_2662_, lean_object* v_domain_2663_, lean_object* v___x_2664_, lean_object* v_type_2665_, lean_object* v___x_2666_, lean_object* v_x_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v___x_791__boxed_2673_; lean_object* v_res_2674_; 
v___x_791__boxed_2673_ = lean_unbox(v___x_2666_);
v_res_2674_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0(v_a_2662_, v_domain_2663_, v___x_2664_, v_type_2665_, v___x_791__boxed_2673_, v_x_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___x_2664_);
lean_dec(v_a_2662_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(lean_object* v_a_2675_, lean_object* v_domain_2676_, lean_object* v_type_2677_, size_t v_sz_2678_, size_t v_i_2679_, lean_object* v_bs_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v___x_2686_; 
v___x_2686_ = lean_usize_dec_lt(v_i_2679_, v_sz_2678_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; 
lean_dec_ref(v_type_2677_);
lean_dec_ref(v_domain_2676_);
lean_dec(v_a_2675_);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v_bs_2680_);
return v___x_2687_;
}
else
{
lean_object* v_v_2688_; lean_object* v___x_2689_; lean_object* v_bs_x27_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___f_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_v_2688_ = lean_array_uget(v_bs_2680_, v_i_2679_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v_bs_x27_2690_ = lean_array_uset(v_bs_2680_, v_i_2679_, v___x_2689_);
v___x_2691_ = lean_usize_to_nat(v_i_2679_);
v___x_2692_ = lean_box(v___x_2686_);
lean_inc_ref(v_type_2677_);
lean_inc_ref(v_domain_2676_);
lean_inc(v_a_2675_);
v___f_2693_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2693_, 0, v_a_2675_);
lean_closure_set(v___f_2693_, 1, v_domain_2676_);
lean_closure_set(v___f_2693_, 2, v___x_2691_);
lean_closure_set(v___f_2693_, 3, v_type_2677_);
lean_closure_set(v___f_2693_, 4, v___x_2692_);
v___x_2694_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_uncurry___closed__2));
v___x_2695_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_2694_, v_v_2688_, v___f_2693_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; size_t v___x_2697_; size_t v___x_2698_; lean_object* v___x_2699_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = ((size_t)1ULL);
v___x_2698_ = lean_usize_add(v_i_2679_, v___x_2697_);
v___x_2699_ = lean_array_uset(v_bs_x27_2690_, v_i_2679_, v_a_2696_);
v_i_2679_ = v___x_2698_;
v_bs_2680_ = v___x_2699_;
goto _start;
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v_bs_x27_2690_);
lean_dec_ref(v_type_2677_);
lean_dec_ref(v_domain_2676_);
lean_dec(v_a_2675_);
v_a_2701_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2695_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2695_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg___boxed(lean_object* v_a_2709_, lean_object* v_domain_2710_, lean_object* v_type_2711_, lean_object* v_sz_2712_, lean_object* v_i_2713_, lean_object* v_bs_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
size_t v_sz_boxed_2720_; size_t v_i_boxed_2721_; lean_object* v_res_2722_; 
v_sz_boxed_2720_ = lean_unbox_usize(v_sz_2712_);
lean_dec(v_sz_2712_);
v_i_boxed_2721_ = lean_unbox_usize(v_i_2713_);
lean_dec(v_i_2713_);
v_res_2722_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2709_, v_domain_2710_, v_type_2711_, v_sz_boxed_2720_, v_i_boxed_2721_, v_bs_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType(lean_object* v_n_2723_, lean_object* v_type_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; uint8_t v___x_2750_; 
v___x_2750_ = l_Lean_Expr_isForall(v_type_2724_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v___x_2751_ = lean_obj_once(&l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1, &l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1_once, _init_l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType___closed__1);
v___x_2752_ = l_Lean_MessageData_ofExpr(v_type_2724_);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_2753_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
v___y_2731_ = v_a_2725_;
v___y_2732_ = v_a_2726_;
v___y_2733_ = v_a_2727_;
v___y_2734_ = v_a_2728_;
goto v___jp_2730_;
}
v___jp_2730_:
{
lean_object* v_domain_2735_; lean_object* v___x_2736_; 
v_domain_2735_ = l_Lean_Expr_bindingDomain_x21(v_type_2724_);
lean_inc_ref(v_domain_2735_);
v___x_2736_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_2723_, v_domain_2735_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; size_t v_sz_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc_n(v_a_2737_, 2);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = lean_array_mk(v_a_2737_);
v_sz_2739_ = lean_array_size(v___x_2738_);
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2737_, v_domain_2735_, v_type_2724_, v_sz_2739_, v___x_2740_, v___x_2738_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
return v___x_2741_;
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec_ref(v_domain_2735_);
lean_dec_ref(v_type_2724_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_Mutual_curryType___boxed(lean_object* v_n_2763_, lean_object* v_type_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v_n_2763_, v_type_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_n_2763_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(lean_object* v_a_2771_, lean_object* v_domain_2772_, lean_object* v_type_2773_, lean_object* v_as_2774_, size_t v_sz_2775_, size_t v_i_2776_, lean_object* v_bs_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___redArg(v_a_2771_, v_domain_2772_, v_type_2773_, v_sz_2775_, v_i_2776_, v_bs_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0___boxed(lean_object* v_a_2784_, lean_object* v_domain_2785_, lean_object* v_type_2786_, lean_object* v_as_2787_, lean_object* v_sz_2788_, lean_object* v_i_2789_, lean_object* v_bs_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
size_t v_sz_boxed_2796_; size_t v_i_boxed_2797_; lean_object* v_res_2798_; 
v_sz_boxed_2796_ = lean_unbox_usize(v_sz_2788_);
lean_dec(v_sz_2788_);
v_i_boxed_2797_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_res_2798_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_ArgsPacker_Mutual_curryType_spec__0(v_a_2784_, v_domain_2785_, v_type_2786_, v_as_2787_, v_sz_boxed_2796_, v_i_boxed_2797_, v_bs_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec_ref(v_as_2787_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs(lean_object* v_argsPacker_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_array_get_size(v_argsPacker_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_numFuncs___boxed(lean_object* v_argsPacker_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_ArgsPacker_numFuncs(v_argsPacker_2801_);
lean_dec_ref(v_argsPacker_2801_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(size_t v_sz_2803_, size_t v_i_2804_, lean_object* v_bs_2805_){
_start:
{
uint8_t v___x_2806_; 
v___x_2806_ = lean_usize_dec_lt(v_i_2804_, v_sz_2803_);
if (v___x_2806_ == 0)
{
return v_bs_2805_;
}
else
{
lean_object* v_v_2807_; lean_object* v___x_2808_; lean_object* v_bs_x27_2809_; lean_object* v___x_2810_; size_t v___x_2811_; size_t v___x_2812_; lean_object* v___x_2813_; 
v_v_2807_ = lean_array_uget(v_bs_2805_, v_i_2804_);
v___x_2808_ = lean_unsigned_to_nat(0u);
v_bs_x27_2809_ = lean_array_uset(v_bs_2805_, v_i_2804_, v___x_2808_);
v___x_2810_ = lean_array_get_size(v_v_2807_);
lean_dec(v_v_2807_);
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_add(v_i_2804_, v___x_2811_);
v___x_2813_ = lean_array_uset(v_bs_x27_2809_, v_i_2804_, v___x_2810_);
v_i_2804_ = v___x_2812_;
v_bs_2805_ = v___x_2813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0___boxed(lean_object* v_sz_2815_, lean_object* v_i_2816_, lean_object* v_bs_2817_){
_start:
{
size_t v_sz_boxed_2818_; size_t v_i_boxed_2819_; lean_object* v_res_2820_; 
v_sz_boxed_2818_ = lean_unbox_usize(v_sz_2815_);
lean_dec(v_sz_2815_);
v_i_boxed_2819_ = lean_unbox_usize(v_i_2816_);
lean_dec(v_i_2816_);
v_res_2820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_boxed_2818_, v_i_boxed_2819_, v_bs_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_arities(lean_object* v_argsPacker_2821_){
_start:
{
size_t v_sz_2822_; size_t v___x_2823_; lean_object* v___x_2824_; 
v_sz_2822_ = lean_array_size(v_argsPacker_2821_);
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_ArgsPacker_arities_spec__0(v_sz_2822_, v___x_2823_, v_argsPacker_2821_);
return v___x_2824_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0(void){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Array_instInhabited___redArg();
return v___x_2825_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_ArgsPacker_onlyOneUnary(lean_object* v_argsPacker_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2827_ = lean_array_get_size(v_argsPacker_2826_);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_nat_dec_eq(v___x_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
return v___x_2829_;
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2830_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2831_ = lean_unsigned_to_nat(0u);
v___x_2832_ = lean_array_get_borrowed(v___x_2830_, v_argsPacker_2826_, v___x_2831_);
v___x_2833_ = lean_array_get_size(v___x_2832_);
v___x_2834_ = lean_nat_dec_eq(v___x_2833_, v___x_2828_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_onlyOneUnary___boxed(lean_object* v_argsPacker_2835_){
_start:
{
uint8_t v_res_2836_; lean_object* v_r_2837_; 
v_res_2836_ = l_Lean_Meta_ArgsPacker_onlyOneUnary(v_argsPacker_2835_);
lean_dec_ref(v_argsPacker_2835_);
v_r_2837_ = lean_box(v_res_2836_);
return v_r_2837_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__2(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2840_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__1));
v___x_2841_ = lean_unsigned_to_nat(2u);
v___x_2842_ = lean_unsigned_to_nat(479u);
v___x_2843_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2844_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2845_ = l_mkPanicMessageWithDecl(v___x_2844_, v___x_2843_, v___x_2842_, v___x_2841_, v___x_2840_);
return v___x_2845_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_pack___closed__4(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2847_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__3));
v___x_2848_ = lean_unsigned_to_nat(2u);
v___x_2849_ = lean_unsigned_to_nat(480u);
v___x_2850_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_pack___closed__0));
v___x_2851_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_2852_ = l_mkPanicMessageWithDecl(v___x_2851_, v___x_2850_, v___x_2849_, v___x_2848_, v___x_2847_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack(lean_object* v_argsPacker_2853_, lean_object* v_domain_2854_, lean_object* v_fidx_2855_, lean_object* v_args_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2862_ = lean_array_get_size(v_argsPacker_2853_);
v___x_2863_ = lean_nat_dec_lt(v_fidx_2855_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec(v_fidx_2855_);
lean_dec_ref(v_domain_2854_);
v___x_2864_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__2, &l_Lean_Meta_ArgsPacker_pack___closed__2_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__2);
v___x_2865_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2864_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2865_;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2866_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2867_ = lean_array_get_size(v_args_2856_);
v___x_2868_ = lean_array_get_borrowed(v___x_2866_, v_argsPacker_2853_, v_fidx_2855_);
v___x_2869_ = lean_array_get_size(v___x_2868_);
v___x_2870_ = lean_nat_dec_eq(v___x_2867_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec(v_fidx_2855_);
lean_dec_ref(v_domain_2854_);
v___x_2871_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_pack___closed__4, &l_Lean_Meta_ArgsPacker_pack___closed__4_once, _init_l_Lean_Meta_ArgsPacker_pack___closed__4);
v___x_2872_ = l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0(v___x_2871_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_domain_2854_);
v___x_2874_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v___x_2862_, v_domain_2854_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
lean_inc(v_fidx_2855_);
v___x_2876_ = l_List_get_x21Internal___redArg(v___x_2873_, v_a_2875_, v_fidx_2855_);
lean_dec(v_a_2875_);
v___x_2877_ = l_Lean_Meta_ArgsPacker_Unary_pack(v___x_2876_, v_args_2856_);
lean_dec(v___x_2876_);
v___x_2878_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_2862_, v_domain_2854_, v_fidx_2855_, v___x_2877_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
lean_dec(v_fidx_2855_);
return v___x_2878_;
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_fidx_2855_);
lean_dec_ref(v_domain_2854_);
v_a_2879_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2874_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2874_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_pack___boxed(lean_object* v_argsPacker_2887_, lean_object* v_domain_2888_, lean_object* v_fidx_2889_, lean_object* v_args_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_Meta_ArgsPacker_pack(v_argsPacker_2887_, v_domain_2888_, v_fidx_2889_, v_args_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec_ref(v_args_2890_);
lean_dec_ref(v_argsPacker_2887_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object* v_argsPacker_2897_, lean_object* v_e_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_array_get_size(v_argsPacker_2897_);
v___x_2900_ = l_Lean_Meta_ArgsPacker_Mutual_unpack(v___x_2899_, v_e_2898_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_box(0);
return v___x_2901_;
}
else
{
lean_object* v_val_2902_; lean_object* v_fst_2903_; lean_object* v_snd_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2924_; 
v_val_2902_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_val_2902_);
lean_dec_ref_known(v___x_2900_, 1);
v_fst_2903_ = lean_ctor_get(v_val_2902_, 0);
v_snd_2904_ = lean_ctor_get(v_val_2902_, 1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_val_2902_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2906_ = v_val_2902_;
v_isShared_2907_ = v_isSharedCheck_2924_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_snd_2904_);
lean_inc(v_fst_2903_);
lean_dec(v_val_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2924_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2908_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v___x_2909_ = lean_array_get_borrowed(v___x_2908_, v_argsPacker_2897_, v_fst_2903_);
v___x_2910_ = lean_array_get_size(v___x_2909_);
v___x_2911_ = l_Lean_Meta_ArgsPacker_Unary_unpack(v___x_2910_, v_snd_2904_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v___x_2912_; 
lean_del_object(v___x_2906_);
lean_dec(v_fst_2903_);
v___x_2912_ = lean_box(0);
return v___x_2912_;
}
else
{
lean_object* v_val_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2923_; 
v_val_2913_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2915_ = v___x_2911_;
v_isShared_2916_ = v_isSharedCheck_2923_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_val_2913_);
lean_dec(v___x_2911_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2923_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 1, v_val_2913_);
v___x_2918_ = v___x_2906_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_fst_2903_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_val_2913_);
v___x_2918_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2920_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2918_);
v___x_2920_ = v___x_2915_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_unpack___boxed(lean_object* v_argsPacker_2925_, lean_object* v_e_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_2925_, v_e_2926_);
lean_dec_ref(v_argsPacker_2925_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(lean_object* v_as_2928_, lean_object* v_bs_2929_, lean_object* v_i_2930_, lean_object* v_cs_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2937_ = lean_array_get_size(v_as_2928_);
v___x_2938_ = lean_nat_dec_lt(v_i_2930_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
lean_dec(v_i_2930_);
v___x_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_cs_2931_);
return v___x_2939_;
}
else
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_bs_2929_);
v___x_2941_ = lean_nat_dec_lt(v_i_2930_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec(v_i_2930_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_cs_2931_);
return v___x_2942_;
}
else
{
lean_object* v_a_2943_; lean_object* v_b_2944_; lean_object* v___x_2945_; 
v_a_2943_ = lean_array_fget_borrowed(v_as_2928_, v_i_2930_);
v_b_2944_ = lean_array_fget_borrowed(v_bs_2929_, v_i_2930_);
lean_inc(v_b_2944_);
lean_inc(v_a_2943_);
v___x_2945_ = l_Lean_Meta_ArgsPacker_Unary_uncurryType(v_a_2943_, v_b_2944_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = lean_unsigned_to_nat(1u);
v___x_2948_ = lean_nat_add(v_i_2930_, v___x_2947_);
lean_dec(v_i_2930_);
v___x_2949_ = lean_array_push(v_cs_2931_, v_a_2946_);
v_i_2930_ = v___x_2948_;
v_cs_2931_ = v___x_2949_;
goto _start;
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref(v_cs_2931_);
lean_dec(v_i_2930_);
v_a_2951_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2945_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2945_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0___boxed(lean_object* v_as_2959_, lean_object* v_bs_2960_, lean_object* v_i_2961_, lean_object* v_cs_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_as_2959_, v_bs_2960_, v_i_2961_, v_cs_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v_bs_2960_);
lean_dec_ref(v_as_2959_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType(lean_object* v_argsPacker_2969_, lean_object* v_types_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = lean_unsigned_to_nat(0u);
v___x_2977_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_2978_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurryType_spec__0(v_argsPacker_2969_, v_types_2970_, v___x_2976_, v___x_2977_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryType(v_a_2979_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_2980_;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_a_2981_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2978_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2978_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryType___boxed(lean_object* v_argsPacker_2989_, lean_object* v_types_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Meta_ArgsPacker_uncurryType(v_argsPacker_2989_, v_types_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec_ref(v_types_2990_);
lean_dec_ref(v_argsPacker_2989_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(lean_object* v_as_2997_, lean_object* v_bs_2998_, lean_object* v_i_2999_, lean_object* v_cs_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = lean_array_get_size(v_as_2997_);
v___x_3007_ = lean_nat_dec_lt(v_i_2999_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec(v_i_2999_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_cs_3000_);
return v___x_3008_;
}
else
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = lean_array_get_size(v_bs_2998_);
v___x_3010_ = lean_nat_dec_lt(v_i_2999_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; 
lean_dec(v_i_2999_);
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_cs_3000_);
return v___x_3011_;
}
else
{
lean_object* v_a_3012_; lean_object* v_b_3013_; lean_object* v___x_3014_; 
v_a_3012_ = lean_array_fget_borrowed(v_as_2997_, v_i_2999_);
v_b_3013_ = lean_array_fget_borrowed(v_bs_2998_, v_i_2999_);
lean_inc(v_b_3013_);
lean_inc(v_a_3012_);
v___x_3014_ = l_Lean_Meta_ArgsPacker_Unary_uncurry(v_a_3012_, v_b_3013_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = lean_unsigned_to_nat(1u);
v___x_3017_ = lean_nat_add(v_i_2999_, v___x_3016_);
lean_dec(v_i_2999_);
v___x_3018_ = lean_array_push(v_cs_3000_, v_a_3015_);
v_i_2999_ = v___x_3017_;
v_cs_3000_ = v___x_3018_;
goto _start;
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec_ref(v_cs_3000_);
lean_dec(v_i_2999_);
v_a_3020_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3014_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3014_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0___boxed(lean_object* v_as_3028_, lean_object* v_bs_3029_, lean_object* v_i_3030_, lean_object* v_cs_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_as_3028_, v_bs_3029_, v_i_3030_, v_cs_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v_bs_3029_);
lean_dec_ref(v_as_3028_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry(lean_object* v_argsPacker_3038_, lean_object* v_es_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3047_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3038_, v_es_3039_, v___x_3045_, v___x_3046_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___x_3049_ = l_Lean_Meta_ArgsPacker_Mutual_uncurry(v_a_3048_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
return v___x_3049_;
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
v_a_3050_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3047_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3047_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurry___boxed(lean_object* v_argsPacker_3058_, lean_object* v_es_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Meta_ArgsPacker_uncurry(v_argsPacker_3058_, v_es_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec_ref(v_es_3059_);
lean_dec_ref(v_argsPacker_3058_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType(lean_object* v_argsPacker_3066_, lean_object* v_resultType_3067_, lean_object* v_es_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3076_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3066_, v_es_3068_, v___x_3074_, v___x_3075_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryWithType(v_resultType_3067_, v_a_3077_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
return v___x_3078_;
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v_resultType_3067_);
v_a_3079_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3076_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3076_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryWithType___boxed(lean_object* v_argsPacker_3087_, lean_object* v_resultType_3088_, lean_object* v_es_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3087_, v_resultType_3088_, v_es_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec_ref(v_es_3089_);
lean_dec_ref(v_argsPacker_3087_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND(lean_object* v_argsPacker_3096_, lean_object* v_es_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = lean_unsigned_to_nat(0u);
v___x_3104_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3105_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_uncurry_spec__0(v_argsPacker_3096_, v_es_3097_, v___x_3103_, v___x_3104_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3107_ = l_Lean_Meta_ArgsPacker_Mutual_uncurryND(v_a_3106_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
return v___x_3107_;
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
v_a_3108_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3105_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3105_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_uncurryND___boxed(lean_object* v_argsPacker_3116_, lean_object* v_es_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_Meta_ArgsPacker_uncurryND(v_argsPacker_3116_, v_es_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_);
lean_dec(v_a_3121_);
lean_dec_ref(v_a_3120_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
lean_dec_ref(v_es_3117_);
lean_dec_ref(v_argsPacker_3116_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(lean_object* v_msg_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___f_3130_; lean_object* v___x_920__overap_3131_; lean_object* v___x_3132_; 
v___f_3130_ = ((lean_object*)(l_panic___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__0___closed__0));
v___x_920__overap_3131_ = lean_panic_fn_borrowed(v___f_3130_, v_msg_3124_);
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
v___x_3132_ = lean_apply_5(v___x_920__overap_3131_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, lean_box(0));
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0___boxed(lean_object* v_msg_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v_msg_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0(lean_object* v_a_3140_, lean_object* v___x_3141_, lean_object* v_i_3142_, lean_object* v_e_3143_, lean_object* v_x_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = l_List_lengthTR___redArg(v_a_3140_);
lean_inc_ref(v_x_3144_);
v___x_3151_ = l_Lean_Meta_ArgsPacker_Mutual_pack(v___x_3150_, v___x_3141_, v_i_3142_, v_x_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___x_3150_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; uint8_t v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v___x_3153_ = lean_unsigned_to_nat(1u);
v___x_3154_ = lean_mk_empty_array_with_capacity(v___x_3153_);
lean_inc_ref(v___x_3154_);
v___x_3155_ = lean_array_push(v___x_3154_, v_x_3144_);
v___x_3156_ = lean_array_push(v___x_3154_, v_a_3152_);
v___x_3157_ = l_Lean_Expr_beta(v_e_3143_, v___x_3156_);
v___x_3158_ = 0;
v___x_3159_ = 1;
v___x_3160_ = 1;
v___x_3161_ = l_Lean_Meta_mkLambdaFVars(v___x_3155_, v___x_3157_, v___x_3158_, v___x_3159_, v___x_3158_, v___x_3159_, v___x_3160_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec_ref(v___x_3155_);
return v___x_3161_;
}
else
{
lean_dec_ref(v_x_3144_);
lean_dec_ref(v_e_3143_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed(lean_object* v_a_3162_, lean_object* v___x_3163_, lean_object* v_i_3164_, lean_object* v_e_3165_, lean_object* v_x_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Meta_ArgsPacker_curryProj___lam__0(v_a_3162_, v___x_3163_, v_i_3164_, v_e_3165_, v_x_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v_i_3164_);
lean_dec(v_a_3162_);
return v_res_3172_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__0));
v___x_3175_ = l_Lean_stringToMessageData(v___x_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3178_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__3));
v___x_3179_ = lean_unsigned_to_nat(4u);
v___x_3180_ = lean_unsigned_to_nat(545u);
v___x_3181_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryProj___closed__2));
v___x_3182_ = ((lean_object*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_pack_go___closed__0));
v___x_3183_ = l_mkPanicMessageWithDecl(v___x_3182_, v___x_3181_, v___x_3180_, v___x_3179_, v___x_3178_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj(lean_object* v_argsPacker_3184_, lean_object* v_e_3185_, lean_object* v_i_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v_n_3194_; lean_object* v___x_3195_; 
v___x_3192_ = l_Lean_instInhabitedExpr;
v___x_3193_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0, &l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0_once, _init_l_Lean_Meta_ArgsPacker_onlyOneUnary___closed__0);
v_n_3194_ = lean_array_get_size(v_argsPacker_3184_);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3189_);
lean_inc(v_a_3188_);
lean_inc_ref(v_a_3187_);
lean_inc_ref(v_e_3185_);
v___x_3195_ = lean_infer_type(v_e_3185_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3197_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3189_);
lean_inc(v_a_3188_);
lean_inc_ref(v_a_3187_);
v___x_3197_ = lean_whnf(v_a_3196_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; uint8_t v___x_3241_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3241_ = l_Lean_Expr_isForall(v_a_3198_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__4, &l_Lean_Meta_ArgsPacker_curryProj___closed__4_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__4);
v___x_3243_ = l_panic___at___00Lean_Meta_ArgsPacker_curryProj_spec__0(v___x_3242_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_dec_ref_known(v___x_3243_, 1);
v___y_3213_ = v_a_3187_;
v___y_3214_ = v_a_3188_;
v___y_3215_ = v_a_3189_;
v___y_3216_ = v_a_3190_;
goto v___jp_3212_;
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v_a_3198_);
lean_dec(v_i_3186_);
lean_dec_ref(v_e_3185_);
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
v___y_3213_ = v_a_3187_;
v___y_3214_ = v_a_3188_;
v___y_3215_ = v_a_3189_;
v___y_3216_ = v_a_3190_;
goto v___jp_3212_;
}
v___jp_3199_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_inc(v_i_3186_);
v___x_3206_ = l_List_get_x21Internal___redArg(v___x_3192_, v___y_3201_, v_i_3186_);
lean_dec(v___y_3201_);
v___x_3207_ = l_Lean_Expr_bindingName_x21(v_a_3198_);
lean_dec(v_a_3198_);
v___x_3208_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3207_, v___x_3206_, v___y_3200_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = lean_array_get_borrowed(v___x_3193_, v_argsPacker_3184_, v_i_3186_);
lean_dec(v_i_3186_);
lean_inc(v___x_3210_);
v___x_3211_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curry(v___x_3210_, v_a_3209_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3211_;
}
else
{
lean_dec(v_i_3186_);
return v___x_3208_;
}
}
v___jp_3212_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = l_Lean_Expr_bindingDomain_x21(v_a_3198_);
lean_inc_ref(v___x_3217_);
v___x_3218_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Mutual_unpackType(v_n_3194_, v___x_3217_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___f_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc_n(v_a_3219_, 2);
lean_dec_ref_known(v___x_3218_, 1);
lean_inc(v_i_3186_);
v___f_3220_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryProj___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3220_, 0, v_a_3219_);
lean_closure_set(v___f_3220_, 1, v___x_3217_);
lean_closure_set(v___f_3220_, 2, v_i_3186_);
lean_closure_set(v___f_3220_, 3, v_e_3185_);
v___x_3221_ = l_List_lengthTR___redArg(v_a_3219_);
v___x_3222_ = lean_nat_dec_lt(v_i_3186_, v___x_3221_);
lean_dec(v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref(v___f_3220_);
lean_dec(v_a_3219_);
lean_dec(v_a_3198_);
lean_dec(v_i_3186_);
v___x_3223_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryProj___closed__1, &l_Lean_Meta_ArgsPacker_curryProj___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryProj___closed__1);
v___x_3224_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3223_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3224_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
else
{
v___y_3200_ = v___f_3220_;
v___y_3201_ = v_a_3219_;
v___y_3202_ = v___y_3213_;
v___y_3203_ = v___y_3214_;
v___y_3204_ = v___y_3215_;
v___y_3205_ = v___y_3216_;
goto v___jp_3199_;
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec_ref(v___x_3217_);
lean_dec(v_a_3198_);
lean_dec(v_i_3186_);
lean_dec_ref(v_e_3185_);
v_a_3233_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3218_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3218_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
}
else
{
lean_dec(v_i_3186_);
lean_dec_ref(v_e_3185_);
return v___x_3197_;
}
}
else
{
lean_dec(v_i_3186_);
lean_dec_ref(v_e_3185_);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryProj___boxed(lean_object* v_argsPacker_3252_, lean_object* v_e_3253_, lean_object* v_i_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3252_, v_e_3253_, v_i_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
lean_dec_ref(v_argsPacker_3252_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(lean_object* v_as_3261_, lean_object* v_bs_3262_, lean_object* v_i_3263_, lean_object* v_cs_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = lean_array_get_size(v_as_3261_);
v___x_3271_ = lean_nat_dec_lt(v_i_3263_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; 
lean_dec(v_i_3263_);
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_cs_3264_);
return v___x_3272_;
}
else
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = lean_array_get_size(v_bs_3262_);
v___x_3274_ = lean_nat_dec_lt(v_i_3263_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; 
lean_dec(v_i_3263_);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_cs_3264_);
return v___x_3275_;
}
else
{
lean_object* v_a_3276_; lean_object* v_b_3277_; lean_object* v___x_3278_; 
v_a_3276_ = lean_array_fget_borrowed(v_as_3261_, v_i_3263_);
v_b_3277_ = lean_array_fget_borrowed(v_bs_3262_, v_i_3263_);
lean_inc(v_b_3277_);
lean_inc(v_a_3276_);
v___x_3278_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_curryType(v_a_3276_, v_b_3277_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v___x_3280_ = lean_unsigned_to_nat(1u);
v___x_3281_ = lean_nat_add(v_i_3263_, v___x_3280_);
lean_dec(v_i_3263_);
v___x_3282_ = lean_array_push(v_cs_3264_, v_a_3279_);
v_i_3263_ = v___x_3281_;
v_cs_3264_ = v___x_3282_;
goto _start;
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v_cs_3264_);
lean_dec(v_i_3263_);
v_a_3284_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3278_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3278_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0___boxed(lean_object* v_as_3292_, lean_object* v_bs_3293_, lean_object* v_i_3294_, lean_object* v_cs_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_as_3292_, v_bs_3293_, v_i_3294_, v_cs_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v_bs_3293_);
lean_dec_ref(v_as_3292_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType(lean_object* v_argsPacker_3302_, lean_object* v_t_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = lean_array_get_size(v_argsPacker_3302_);
v___x_3310_ = l_Lean_Meta_ArgsPacker_Mutual_curryType(v___x_3309_, v_t_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
v___x_3312_ = lean_unsigned_to_nat(0u);
v___x_3313_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3314_ = l_Array_zipWithMAux___at___00Lean_Meta_ArgsPacker_curryType_spec__0(v_argsPacker_3302_, v_a_3311_, v___x_3312_, v___x_3313_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
lean_dec(v_a_3311_);
return v___x_3314_;
}
else
{
return v___x_3310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryType___boxed(lean_object* v_argsPacker_3315_, lean_object* v_t_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3315_, v_t_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec_ref(v_argsPacker_3315_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(lean_object* v_upperBound_3323_, lean_object* v_argsPacker_3324_, lean_object* v_e_3325_, lean_object* v_a_3326_, lean_object* v_b_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
uint8_t v___x_3333_; 
v___x_3333_ = lean_nat_dec_lt(v_a_3326_, v_upperBound_3323_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
lean_dec(v_a_3326_);
lean_dec_ref(v_e_3325_);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_b_3327_);
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; 
lean_inc(v_a_3326_);
lean_inc_ref(v_e_3325_);
v___x_3335_ = l_Lean_Meta_ArgsPacker_curryProj(v_argsPacker_3324_, v_e_3325_, v_a_3326_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = lean_array_push(v_b_3327_, v_a_3336_);
v___x_3338_ = lean_unsigned_to_nat(1u);
v___x_3339_ = lean_nat_add(v_a_3326_, v___x_3338_);
lean_dec(v_a_3326_);
v_a_3326_ = v___x_3339_;
v_b_3327_ = v___x_3337_;
goto _start;
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v_b_3327_);
lean_dec(v_a_3326_);
lean_dec_ref(v_e_3325_);
v_a_3341_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3335_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3335_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg___boxed(lean_object* v_upperBound_3349_, lean_object* v_argsPacker_3350_, lean_object* v_e_3351_, lean_object* v_a_3352_, lean_object* v_b_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3349_, v_argsPacker_3350_, v_e_3351_, v_a_3352_, v_b_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec_ref(v_argsPacker_3350_);
lean_dec(v_upperBound_3349_);
return v_res_3359_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curry___closed__0(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = l_Lean_Level_ofNat(v___x_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object* v_argsPacker_3362_, lean_object* v_e_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v_es_3371_; lean_object* v___x_3372_; 
v___x_3369_ = lean_array_get_size(v_argsPacker_3362_);
v___x_3370_ = lean_unsigned_to_nat(0u);
v_es_3371_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3372_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v___x_3369_, v_argsPacker_3362_, v_e_3363_, v___x_3370_, v_es_3371_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v___x_3374_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curry___closed__0, &l_Lean_Meta_ArgsPacker_curry___closed__0_once, _init_l_Lean_Meta_ArgsPacker_curry___closed__0);
v___x_3375_ = l_Lean_Meta_PProdN_mk(v___x_3374_, v_a_3373_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
return v___x_3375_;
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_a_3376_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3372_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3372_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curry___boxed(lean_object* v_argsPacker_3384_, lean_object* v_e_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_Meta_ArgsPacker_curry(v_argsPacker_3384_, v_e_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec_ref(v_argsPacker_3384_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(lean_object* v_upperBound_3392_, lean_object* v_argsPacker_3393_, lean_object* v_e_3394_, lean_object* v_inst_3395_, lean_object* v_R_3396_, lean_object* v_a_3397_, lean_object* v_b_3398_, lean_object* v_c_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___redArg(v_upperBound_3392_, v_argsPacker_3393_, v_e_3394_, v_a_3397_, v_b_3398_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0___boxed(lean_object* v_upperBound_3406_, lean_object* v_argsPacker_3407_, lean_object* v_e_3408_, lean_object* v_inst_3409_, lean_object* v_R_3410_, lean_object* v_a_3411_, lean_object* v_b_3412_, lean_object* v_c_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_ArgsPacker_curry_spec__0(v_upperBound_3406_, v_argsPacker_3407_, v_e_3408_, v_inst_3409_, v_R_3410_, v_a_3411_, v_b_3412_, v_c_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v_argsPacker_3407_);
lean_dec(v_upperBound_3406_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed(lean_object* v_a_3420_, lean_object* v_argsPacker_3421_, lean_object* v_name_3422_, lean_object* v_k_3423_, lean_object* v_tail_3424_, lean_object* v_x_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(v_a_3420_, v_argsPacker_3421_, v_name_3422_, v_k_3423_, v_tail_3424_, v_x_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(lean_object* v_argsPacker_3432_, lean_object* v_name_3433_, lean_object* v_k_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
if (lean_obj_tag(v_a_3435_) == 0)
{
lean_object* v___x_3442_; 
lean_dec(v_name_3433_);
lean_dec_ref(v_argsPacker_3432_);
lean_inc(v_a_3440_);
lean_inc_ref(v_a_3439_);
lean_inc(v_a_3438_);
lean_inc_ref(v_a_3437_);
v___x_3442_ = lean_apply_6(v_k_3434_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, lean_box(0));
return v___x_3442_;
}
else
{
lean_object* v_head_3443_; lean_object* v_tail_3444_; lean_object* v___f_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v_head_3443_ = lean_ctor_get(v_a_3435_, 0);
lean_inc(v_head_3443_);
v_tail_3444_ = lean_ctor_get(v_a_3435_, 1);
lean_inc(v_tail_3444_);
lean_dec_ref_known(v_a_3435_, 2);
lean_inc(v_name_3433_);
lean_inc_ref(v_argsPacker_3432_);
lean_inc_ref(v_a_3436_);
v___f_3445_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3445_, 0, v_a_3436_);
lean_closure_set(v___f_3445_, 1, v_argsPacker_3432_);
lean_closure_set(v___f_3445_, 2, v_name_3433_);
lean_closure_set(v___f_3445_, 3, v_k_3434_);
lean_closure_set(v___f_3445_, 4, v_tail_3444_);
v___x_3446_ = lean_array_get_size(v_argsPacker_3432_);
lean_dec_ref(v_argsPacker_3432_);
v___x_3447_ = lean_unsigned_to_nat(1u);
v___x_3448_ = lean_nat_dec_eq(v___x_3446_, v___x_3447_);
if (v___x_3448_ == 0)
{
uint8_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3449_ = 1;
v___x_3450_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3433_, v___x_3449_);
v___x_3451_ = lean_array_get_size(v_a_3436_);
lean_dec_ref(v_a_3436_);
v___x_3452_ = lean_nat_add(v___x_3451_, v___x_3447_);
v___x_3453_ = l_Nat_reprFast(v___x_3452_);
v___x_3454_ = lean_string_append(v___x_3450_, v___x_3453_);
lean_dec_ref(v___x_3453_);
v___x_3455_ = lean_box(0);
v___x_3456_ = l_Lean_Name_str___override(v___x_3455_, v___x_3454_);
v___x_3457_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v___x_3456_, v_head_3443_, v___f_3445_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
return v___x_3457_;
}
else
{
lean_object* v___x_3458_; 
lean_dec_ref(v_a_3436_);
v___x_3458_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_ArgsPacker_Unary_uncurryType_spec__1___redArg(v_name_3433_, v_head_3443_, v___f_3445_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
return v___x_3458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___lam__0(lean_object* v_a_3459_, lean_object* v_argsPacker_3460_, lean_object* v_name_3461_, lean_object* v_k_3462_, lean_object* v_tail_3463_, lean_object* v_x_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = lean_array_push(v_a_3459_, v_x_3464_);
v___x_3471_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3460_, v_name_3461_, v_k_3462_, v_tail_3463_, v___x_3470_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg___boxed(lean_object* v_argsPacker_3472_, lean_object* v_name_3473_, lean_object* v_k_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3472_, v_name_3473_, v_k_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(lean_object* v_00_u03b1_3483_, lean_object* v_argsPacker_3484_, lean_object* v_name_3485_, lean_object* v_k_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3484_, v_name_3485_, v_k_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___boxed(lean_object* v_00_u03b1_3495_, lean_object* v_argsPacker_3496_, lean_object* v_name_3497_, lean_object* v_k_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go(v_00_u03b1_3495_, v_argsPacker_3496_, v_name_3497_, v_k_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
lean_dec(v_a_3504_);
lean_dec_ref(v_a_3503_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(lean_object* v_argsPacker_3507_, lean_object* v_name_3508_, lean_object* v_type_3509_, lean_object* v_k_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_Meta_ArgsPacker_curryType(v_argsPacker_3507_, v_type_3509_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
v___x_3518_ = lean_array_to_list(v_a_3517_);
v___x_3519_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_Unary_unpack___closed__0));
v___x_3520_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl_go___redArg(v_argsPacker_3507_, v_name_3508_, v_k_3510_, v___x_3518_, v___x_3519_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
return v___x_3520_;
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec_ref(v_k_3510_);
lean_dec(v_name_3508_);
lean_dec_ref(v_argsPacker_3507_);
v_a_3521_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3516_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3516_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg___boxed(lean_object* v_argsPacker_3529_, lean_object* v_name_3530_, lean_object* v_type_3531_, lean_object* v_k_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3529_, v_name_3530_, v_type_3531_, v_k_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(lean_object* v_00_u03b1_3539_, lean_object* v_argsPacker_3540_, lean_object* v_name_3541_, lean_object* v_type_3542_, lean_object* v_k_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3540_, v_name_3541_, v_type_3542_, v_k_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___boxed(lean_object* v_00_u03b1_3550_, lean_object* v_argsPacker_3551_, lean_object* v_name_3552_, lean_object* v_type_3553_, lean_object* v_k_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl(v_00_u03b1_3550_, v_argsPacker_3551_, v_name_3552_, v_type_3553_, v_k_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(lean_object* v_argsPacker_3561_, lean_object* v_packedMotiveType_3562_, lean_object* v_type_3563_, lean_object* v_value_3564_, lean_object* v_k_3565_, lean_object* v_motives_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Lean_Meta_ArgsPacker_uncurryWithType(v_argsPacker_3561_, v_packedMotiveType_3562_, v_motives_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc_n(v_a_3573_, 2);
lean_dec_ref_known(v___x_3572_, 1);
v___x_3574_ = lean_unsigned_to_nat(1u);
v___x_3575_ = lean_mk_empty_array_with_capacity(v___x_3574_);
v___x_3576_ = lean_array_push(v___x_3575_, v_a_3573_);
v___x_3577_ = l_Lean_Meta_instantiateForall(v_type_3563_, v___x_3576_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec_ref(v___x_3576_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = l_Lean_Expr_app___override(v_value_3564_, v_a_3573_);
lean_inc(v___y_3570_);
lean_inc_ref(v___y_3569_);
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3567_);
v___x_3580_ = lean_apply_8(v_k_3565_, v_motives_3566_, v___x_3579_, v_a_3578_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, lean_box(0));
return v___x_3580_;
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v_a_3573_);
lean_dec_ref(v_motives_3566_);
lean_dec_ref(v_k_3565_);
lean_dec_ref(v_value_3564_);
v_a_3581_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3577_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3577_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref(v_motives_3566_);
lean_dec_ref(v_k_3565_);
lean_dec_ref(v_value_3564_);
lean_dec_ref(v_type_3563_);
v_a_3589_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3572_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3572_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed(lean_object* v_argsPacker_3597_, lean_object* v_packedMotiveType_3598_, lean_object* v_type_3599_, lean_object* v_value_3600_, lean_object* v_k_3601_, lean_object* v_motives_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0(v_argsPacker_3597_, v_packedMotiveType_3598_, v_type_3599_, v_value_3600_, v_k_3601_, v_motives_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v_argsPacker_3597_);
return v_res_3608_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__0));
v___x_3611_ = l_Lean_stringToMessageData(v___x_3610_);
return v___x_3611_;
}
}
static lean_object* _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__2));
v___x_3614_ = l_Lean_stringToMessageData(v___x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg(lean_object* v_argsPacker_3615_, lean_object* v_value_3616_, lean_object* v_type_3617_, lean_object* v_k_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; uint8_t v___x_3653_; 
v___x_3653_ = l_Lean_Expr_isForall(v_type_3617_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec_ref(v_k_3618_);
lean_dec_ref(v_value_3616_);
lean_dec_ref(v_argsPacker_3615_);
v___x_3654_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__3);
v___x_3655_ = l_Lean_MessageData_ofExpr(v_type_3617_);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3656_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_);
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
else
{
v___y_3634_ = v_a_3619_;
v___y_3635_ = v_a_3620_;
v___y_3636_ = v_a_3621_;
v___y_3637_ = v_a_3622_;
goto v___jp_3633_;
}
v___jp_3624_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = l_Lean_Expr_bindingName_x21(v_type_3617_);
lean_dec_ref(v_type_3617_);
v___x_3632_ = l___private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_withCurriedDecl___redArg(v_argsPacker_3615_, v___x_3631_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3632_;
}
v___jp_3633_:
{
lean_object* v_packedMotiveType_3638_; lean_object* v___f_3639_; uint8_t v___x_3640_; 
v_packedMotiveType_3638_ = l_Lean_Expr_bindingDomain_x21(v_type_3617_);
lean_inc_ref(v_type_3617_);
lean_inc_ref(v_packedMotiveType_3638_);
lean_inc_ref(v_argsPacker_3615_);
v___f_3639_ = lean_alloc_closure((void*)(l_Lean_Meta_ArgsPacker_curryParam___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3639_, 0, v_argsPacker_3615_);
lean_closure_set(v___f_3639_, 1, v_packedMotiveType_3638_);
lean_closure_set(v___f_3639_, 2, v_type_3617_);
lean_closure_set(v___f_3639_, 3, v_value_3616_);
lean_closure_set(v___f_3639_, 4, v_k_3618_);
v___x_3640_ = l_Lean_Expr_isForall(v_packedMotiveType_3638_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec_ref(v___f_3639_);
lean_dec_ref(v_type_3617_);
lean_dec_ref(v_argsPacker_3615_);
v___x_3641_ = lean_obj_once(&l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1, &l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1_once, _init_l_Lean_Meta_ArgsPacker_curryParam___redArg___closed__1);
v___x_3642_ = l_Lean_indentExpr(v_packedMotiveType_3638_);
v___x_3643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3641_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = l_Lean_throwError___at___00__private_Lean_Meta_ArgsPacker_0__Lean_Meta_ArgsPacker_Unary_casesOn_spec__0___redArg(v___x_3643_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
else
{
v___y_3625_ = v_packedMotiveType_3638_;
v___y_3626_ = v___f_3639_;
v___y_3627_ = v___y_3634_;
v___y_3628_ = v___y_3635_;
v___y_3629_ = v___y_3636_;
v___y_3630_ = v___y_3637_;
goto v___jp_3624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___redArg___boxed(lean_object* v_argsPacker_3666_, lean_object* v_value_3667_, lean_object* v_type_3668_, lean_object* v_k_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3666_, v_value_3667_, v_type_3668_, v_k_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_);
lean_dec(v_a_3673_);
lean_dec_ref(v_a_3672_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam(lean_object* v_00_u03b1_3676_, lean_object* v_argsPacker_3677_, lean_object* v_value_3678_, lean_object* v_type_3679_, lean_object* v_k_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_Meta_ArgsPacker_curryParam___redArg(v_argsPacker_3677_, v_value_3678_, v_type_3679_, v_k_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ArgsPacker_curryParam___boxed(lean_object* v_00_u03b1_3687_, lean_object* v_argsPacker_3688_, lean_object* v_value_3689_, lean_object* v_type_3690_, lean_object* v_k_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l_Lean_Meta_ArgsPacker_curryParam(v_00_u03b1_3687_, v_argsPacker_3688_, v_value_3689_, v_type_3690_, v_k_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_);
lean_dec(v_a_3695_);
lean_dec_ref(v_a_3694_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
return v_res_3697_;
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
